(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptRecs LeptSlots LeptSel.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10LeptStderr V10LeptBase.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL7a.
Import V10CL7a.V10LeptSel_iface.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10_code_fhFG.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL8a.
Import V10CL8a.V10LeptSelSegs.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10LeptSelCreate.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoom10.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Ltac fixv' v tac := lazymatch goal with |- msteps _ (mkst (regupd _ _ ?x) _ _ _) _ => first [ constr_eq x v | replace x with v by (symmetry; tac) ] end.
Ltac condR := pin; first [ apply c_eq_refl | vm_compute; reflexivity ].
Ltac sltu0' F D := sn F D; fixv' (Z_to_bv 64 0) ltac:(apply zbv_sltu_ge; lia).
Ltac slti0' F D := sn F D; fixv' (Z_to_bv 64 0) ltac:(apply zbv_slti0; lia).

Lemma slli32_srli32 : forall w, (0 <= w < 2 ^ 31)%Z -> v_srli (v_slli (Z_to_bv 64 w) 32) 32 = Z_to_bv 64 w.
Proof. intros w Hw. rewrite zbv_slli by lia. rewrite zbv_srli by lia. f_equal. apply Z_div_mult. lia. Qed.

Lemma slli32_srli30 : forall w, (0 <= w < 2 ^ 31)%Z -> v_srli (v_slli (Z_to_bv 64 w) 32) 30 = Z_to_bv 64 (4 * w).
Proof.
  intros w Hw. rewrite zbv_slli by lia. rewrite zbv_srli by lia. f_equal.
  replace (w * 2 ^ 32)%Z with ((4 * w) * 2 ^ 30)%Z by lia. apply Z_div_mult. lia.
Qed.

Section SelBrick.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V10Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SegsB.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma bk_A : forall regs m (s h w cy cx ty : Z) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= h < 2 ^ 31)%Z -> (1 <= w < 2 ^ 31)%Z -> (0 <= ty <= 2)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 h -> getr regs 11 = Z_to_bv 64 w ->
    getr regs 12 = Z_to_bv 64 cy -> getr regs 13 = Z_to_bv 64 cx -> getr regs 14 = Z_to_bv 64 ty ->
    exists regs',
      msteps SEGS (mkst regs (0x274cc : word) m rom) (mkst regs' (0x27068 : word) (SCF m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x2757c
      /\ getr regs' 10 = Z_to_bv 64 h /\ getr regs' 11 = Z_to_bv 64 w /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 8 = Z_to_bv 64 ty /\ getr regs' 9 = Z_to_bv 64 cx /\ getr regs' 18 = Z_to_bv 64 cy /\ getr regs' 19 = Z_to_bv 64 h /\ getr regs' 20 = Z_to_bv 64 w
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 12; 15; 18; 19; 20]%list) regs regs'.
  Proof.
    intros regs m s h w cy cx ty ret Hs Hs64 Hh Hw Hty SOK H2 H1 H10 H11 H12 H13 H14.
    eexists. split.
    - zv F_273d0 D_273d0 (Z_to_bv 64 (s - 48)).
      stepST F_273d4 D_273d4 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_273d8 D_273d8 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_273dc D_273dc (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_273e0 D_273e0 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_273e4 D_273e4 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_273e8 D_273e8 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepb_ft F_273ec D_273ec ltac:(condZ).
      stepb_ft F_273f0 D_273f0 ltac:(condZ).
      sn F_273f4 D_273f4.
      stepb_tk F_273f8 D_273f8 ltac:(condZ).
      sn F_27464 D_27464. sn F_27468 D_27468. sn F_2746c D_2746c. sn F_27470 D_27470. sn F_27474 D_27474. sn F_27478 D_27478. sn F_2747c D_2747c.
      unfold SCF. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma bk_B : forall regs m (sel data h w cy cx ty : Z),
    (1 <= sel)%Z -> (sel + 32 < 2 ^ 64)%Z -> (sel mod 8 = 0)%Z -> (1 <= h < 2 ^ 31)%Z -> (0 <= w < 2 ^ 31)%Z -> (1 <= data < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (sel + 16)) 8 = Some (Z_to_le_bytes 8 data) -> store_ok SEGS m (Z_to_bv 64 (sel + 8)) 8 = true ->
    getr regs 10 = Z_to_bv 64 sel -> getr regs 18 = Z_to_bv 64 cy -> getr regs 9 = Z_to_bv 64 cx -> getr regs 8 = Z_to_bv 64 ty ->
    getr regs 19 = Z_to_bv 64 h -> getr regs 20 = Z_to_bv 64 w ->
    exists regs',
      msteps SEGS (mkst regs (0x2757c : word) m rom)
                  (mkst regs' (0x275b0 : word) (wbytes (wbytes m (Z_to_bv 64 (sel + 8)) (word_to_le_bytes 4 (Z_to_bv 64 cy)))
                                                      (Z_to_bv 64 (sel + 12)) (word_to_le_bytes 4 (Z_to_bv 64 cx))) rom)
      /\ getr regs' 10 = Z_to_bv 64 sel /\ getr regs' 11 = Z_to_bv 64 ty /\ getr regs' 12 = Z_to_bv 64 h /\ getr regs' 13 = Z_to_bv 64 0
      /\ getr regs' 14 = Z_to_bv 64 data /\ getr regs' 15 = Z_to_bv 64 w /\ getr regs' 16 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [11; 12; 13; 14; 15; 16]%list) regs regs'.
  Proof.
    intros regs m sel data h w cy cx ty Hs Hs64 ALs Hh Hw Hd Rd SOK H10 H18 H9 H8 H19 H20.
    eexists. split.
    - stepb_ft F_27480 D_27480 ltac:(condZ).                                          (* [comment removed for export] *)
      zand F_27484 D_27484 andi_7 ALs. stepb_ft F_27488 D_27488 ltac:(condZ).          (* [comment removed for export] *)
      stepST F_2748c D_2748c (Z_to_bv 64 (sel + 8)) (Z_to_bv 64 cy) ltac:(sok_in SOK).
      stepST F_27490 D_27490 (Z_to_bv 64 (sel + 12)) (Z_to_bv 64 cx) ltac:(sok_in SOK).
      stepb_ft F_27494 D_27494 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_27498 D_27498. sn F_2749c D_2749c. sn F_274a0 D_274a0.
      stepLD F_274a4 D_274a4 (Z_to_le_bytes 8 data) (Z_to_bv 64 data) ltac:(addr_norm; repeat rdn_peel1; exact Rd) ltac:(apply lez8; lia).
      sn F_274a8 D_274a8. sn F_274ac D_274ac. fixv (Z_to_bv 64 w) ltac:(pin; apply slli32_srli32; lia).
      snez1 F_274b0 D_274b0.                                                          (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma bk_O : forall regs m (data i row w : Z),
    (1 <= data)%Z -> (data + 8 * i + 8 < 2 ^ 64)%Z -> (0 <= i < 2 ^ 31)%Z -> (1 <= row < 2 ^ 64)%Z -> (0 <= w < 2 ^ 31)%Z ->
    (data mod 8 = 0)%Z -> (row mod 4 = 0)%Z ->
    rdn SEGS m (Z_to_bv 64 (data + 8 * i)) 8 = Some (Z_to_le_bytes 8 row) ->
    getr regs 13 = Z_to_bv 64 i -> getr regs 14 = Z_to_bv 64 data -> getr regs 15 = Z_to_bv 64 w -> getr regs 16 = Z_to_bv 64 1 ->
    exists regs',
      msteps SEGS (mkst regs (0x275b0 : word) m rom) (mkst regs' (0x275f0 : word) m rom)
      /\ getr regs' 17 = Z_to_bv 64 row /\ getr regs' 5 = Z_to_bv 64 1 /\ getr regs' 6 = Z_to_bv 64 1 /\ getr regs' 7 = Z_to_bv 64 w
      /\ getr regs' 28 = Z_to_bv 64 row /\ getr regs' 29 = Z_to_bv 64 row
      /\ regs_agree (fun r => In r [5; 6; 7; 17; 28; 29]%list) regs regs'.
  Proof.
    intros regs m data i row w Hd Hd64 Hi Hrow Hw ALd ALr Rr H13 H14 H15 H16.
    assert (ALc : ((data + 8 * i) mod 8 = 0)%Z) by (rewrite Z.mul_comm, Z_mod_plus_full; exact ALd).
    eexists. split.
    - stepiv F_274b4 D_274b4 (Z_to_bv 64 (8 * i)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; lia).
      zv F_274b8 D_274b8 (Z_to_bv 64 (data + 8 * i)).
      seqz0 F_274bc D_274bc.                                                          (* [comment removed for export] *)
      stepb_ft F_274c0 D_274c0 ltac:(condR).                                          (* [comment removed for export] *)
      stepb_ft F_274c4 D_274c4 ltac:(condZ).                                          (* [comment removed for export] *)
      stepb_ft F_274c8 D_274c8 ltac:(condZ).                                          (* [comment removed for export] *)
      zand F_274cc D_274cc andi_7 ALc. stepb_ft F_274d0 D_274d0 ltac:(condZ).          (* [comment removed for export] *)
      stepLD F_274d4 D_274d4 (Z_to_le_bytes 8 row) (Z_to_bv 64 row) ltac:(addr_norm; exact Rr) ltac:(apply lez8; lia).
      snez1 F_274d8 D_274d8.                                                          (* [comment removed for export] *)
      zand F_274dc D_274dc andi_3 ALr.                                                (* [comment removed for export] *)
      stepiv F_274e0 D_274e0 (Z_to_bv 64 1) ltac:(gres; pin; imm_norm; rewrite zbv_seqz by lia; reflexivity).   (* [comment removed for export] *)
      zlit F_274e4 D_274e4 (Z_to_bv 64 1).                                            (* [comment removed for export] *)
      sn F_274e8 D_274e8. sn F_274ec D_274ec. sn F_274f0 D_274f0.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma bk_I_cont : forall regs m (row w j ty : Z),
    (1 <= row)%Z -> (row + 4 * w < 2 ^ 64)%Z -> (0 <= j)%Z -> (j + 1 < w)%Z -> (w < 2 ^ 31)%Z ->
    store_ok SEGS m (Z_to_bv 64 (row + 4 * j)) 4 = true ->
    getr regs 11 = Z_to_bv 64 ty -> getr regs 17 = Z_to_bv 64 row -> getr regs 5 = Z_to_bv 64 1 -> getr regs 6 = Z_to_bv 64 1 ->
    getr regs 7 = Z_to_bv 64 (w - j) -> getr regs 28 = Z_to_bv 64 (row + 4 * j) -> getr regs 29 = Z_to_bv 64 (row + 4 * j) ->
    exists regs',
      msteps SEGS (mkst regs (0x275f0 : word) m rom)
                  (mkst regs' (0x275f0 : word) (wbytes m (Z_to_bv 64 (row + 4 * j)) (word_to_le_bytes 4 (Z_to_bv 64 ty))) rom)
      /\ getr regs' 7 = Z_to_bv 64 (w - (j + 1)) /\ getr regs' 28 = Z_to_bv 64 (row + 4 * (j + 1)) /\ getr regs' 29 = Z_to_bv 64 (row + 4 * (j + 1))
      /\ regs_agree (fun r => In r [7; 28; 29; 30]%list) regs regs'.
  Proof.
    intros regs m row w j ty Hr Hr64 Hj Hj1 Hw SOK H11 H17 H5 H6 H7 H28 H29.
    eexists. split.
    - stepb_ft F_274f4 D_274f4 ltac:(condZ).                                          (* [comment removed for export] *)
      seqz0 F_274f8 D_274f8.                                                          (* [comment removed for export] *)
      zlit F_274fc D_274fc (Z_to_bv 64 1).                                            (* [comment removed for export] *)
      stepb_ft F_27500 D_27500 ltac:(condZ).                                          (* [comment removed for export] *)
      stepb_ft F_27504 D_27504 ltac:(condZ).                                          (* [comment removed for export] *)
      stepST F_27508 D_27508 (Z_to_bv 64 (row + 4 * j)) (Z_to_bv 64 ty) ltac:(store_ok_peel; exact SOK).
      zv F_2750c D_2750c (Z_to_bv 64 (row + 4 * (j + 1))).
      zv F_27510 D_27510 (Z_to_bv 64 (w - (j + 1))).
      zv F_27514 D_27514 (Z_to_bv 64 (row + 4 * (j + 1))).
      stepb_tk F_27518 D_27518 ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma bk_I_last : forall regs m (row w j ty : Z),
    (1 <= row)%Z -> (row + 4 * w < 2 ^ 64)%Z -> (0 <= j)%Z -> (j + 1 = w)%Z -> (w < 2 ^ 31)%Z ->
    store_ok SEGS m (Z_to_bv 64 (row + 4 * j)) 4 = true ->
    getr regs 11 = Z_to_bv 64 ty -> getr regs 17 = Z_to_bv 64 row -> getr regs 5 = Z_to_bv 64 1 -> getr regs 6 = Z_to_bv 64 1 ->
    getr regs 7 = Z_to_bv 64 (w - j) -> getr regs 28 = Z_to_bv 64 (row + 4 * j) -> getr regs 29 = Z_to_bv 64 (row + 4 * j) ->
    exists regs',
      msteps SEGS (mkst regs (0x275f0 : word) m rom)
                  (mkst regs' (0x27618 : word) (wbytes m (Z_to_bv 64 (row + 4 * j)) (word_to_le_bytes 4 (Z_to_bv 64 ty))) rom)
      /\ regs_agree (fun r => In r [7; 28; 29; 30]%list) regs regs'.
  Proof.
    intros regs m row w j ty Hr Hr64 Hj Hj1 Hw SOK H11 H17 H5 H6 H7 H28 H29.
    eexists. split.
    - stepb_ft F_274f4 D_274f4 ltac:(condZ).
      seqz0 F_274f8 D_274f8.
      zlit F_274fc D_274fc (Z_to_bv 64 1).
      stepb_ft F_27500 D_27500 ltac:(condZ).
      stepb_ft F_27504 D_27504 ltac:(condZ).
      stepST F_27508 D_27508 (Z_to_bv 64 (row + 4 * j)) (Z_to_bv 64 ty) ltac:(store_ok_peel; exact SOK).
      zv F_2750c D_2750c (Z_to_bv 64 (row + 4 * (j + 1))).
      zv F_27510 D_27510 (Z_to_bv 64 0).
      zv F_27514 D_27514 (Z_to_bv 64 (row + 4 * (j + 1))).
      stepb_ft F_27518 D_27518 ltac:(condZ).
      apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma bk_N_cont : forall regs m (i h : Z),
    (0 <= i)%Z -> (i + 1 < h)%Z -> (h < 2 ^ 31)%Z -> getr regs 13 = Z_to_bv 64 i -> getr regs 12 = Z_to_bv 64 h ->
    exists regs',
      msteps SEGS (mkst regs (0x27618 : word) m rom) (mkst regs' (0x275b0 : word) m rom)
      /\ getr regs' 13 = Z_to_bv 64 (i + 1) /\ regs_agree (fun r => In r [13]%list) regs regs'.
  Proof.
    intros regs m i h Hi Hi1 Hh H13 H12. eexists. split.
    - zv F_2751c D_2751c (Z_to_bv 64 (i + 1)).
      stepb_tk F_27520 D_27520 ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma bk_N_last : forall regs m (s i h : Z) (ret s0v s1v s2v s3v s4v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= i)%Z -> (i + 1 = h)%Z -> (h < 2 ^ 31)%Z -> ret_ok ret ->
    sccells m s ret s0v s1v s2v s3v s4v ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 13 = Z_to_bv 64 i -> getr regs 12 = Z_to_bv 64 h ->
    exists regs',
      msteps SEGS (mkst regs (0x27618 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = getr regs 10
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 13; 18; 19; 20]%list) regs regs'.
  Proof.
    intros regs m s i h ret s0v s1v s2v s3v s4v Hs Hs64 Hi Hi1 Hh Hret CE H2 H13 H12. destruct CE as (C1 & C2 & C3 & C4 & C5 & C6).
    eexists. split.
    - zv F_2751c D_2751c (Z_to_bv 64 (i + 1)).
      stepb_ft F_27520 D_27520 ltac:(condZ).
      sn F_27524 D_27524.
      stepLD8 F_2754c D_2754c ret. stepLD8 F_27550 D_27550 s0v. stepLD8 F_27554 D_27554 s1v.
      stepLD8 F_27558 D_27558 s2v. stepLD8 F_2755c D_2755c s3v. stepLD8 F_27560 D_27560 s4v.
      zv F_27564 D_27564 (Z_to_bv 64 s).
      stepret F_27568 D_27568 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End SegsB.

(* [comment removed for export] *)
Definition bctx (C : lctx) (A A1 : AS) (md1 : Model) (M1 : word -> option byte) (s sel : Z) (v : selv) : Prop :=
  Cok C /\ (s mod 16 = 0)%Z /\ (c_top C - LSTK + 48 <= s)%Z /\ (s <= c_top C)%Z /\
  W C A1 M1 md1 /\ sel_at (alloc_top (c_vm C)) A1 M1 sel v /\ sel_off A sel v /\ sel_off (c_A0 C) sel v /\ sub_live A A1 /\
  (1 <= v_sx v <= 500)%Z /\ (1 <= v_sy v <= 250)%Z.

Definition outside_rows (v : selv) (x : word) : Prop := forall i, (0 <= i < v_sy v)%Z -> ~ (v_rows v i <= u x < v_rows v i + 4 * v_sx v)%Z.

(* [comment removed for export] *)
Definition bst (C : lctx) (A A1 : AS) (md1 : Model) (m M1 Mi : word -> option byte) (s : Z) (v : selv) (regs : bvmap 5 word) : Prop :=
  W C A1 Mi md1 /\ POSTM C A s m Mi /\
  sccells Mi s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) /\
  (forall x : word, outside_rows v x -> Mi x = M1 x).

(* [comment removed for export] *)
Lemma bst_store : forall C A A1 md1 m M1 Mi s sel v regs (i j ty : Z),
  bctx C A A1 md1 M1 s sel v -> bst C A A1 md1 m M1 Mi s v regs -> (0 <= i < v_sy v)%Z -> (0 <= j < v_sx v)%Z ->
  store_ok SEGS Mi (Z_to_bv 64 (v_rows v i + 4 * j)) 4 = true /\
  bst C A A1 md1 m M1 (wbytes Mi (Z_to_bv 64 (v_rows v i + 4 * j)) (word_to_le_bytes 4 (Z_to_bv 64 ty))) s v regs.
Proof.
  intros C A A1 md1 m M1 Mi s sel v regs i j ty (CK & Hs16 & Hlo & Hhi & HW1 & SA & SO & SO0 & SUB & Hsx & Hsy) (HW & PM & CE & FR) Hi Hj.
  pose proof SA as (_ & _ & _ & _ & _ & _ & _ & _ & ROWS & _). destruct (ROWS i Hi) as (Br & Lr & _).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  destruct Br as (Gr & TOPr & ALr).
  assert (LrA : live A (Z_to_bv 64 (v_rows v i)) = None) by (apply SO; right; right; exists i; split; [exact Hi | reflexivity]).
  assert (Lr0 : live (c_A0 C) (Z_to_bv 64 (v_rows v i)) = None) by (apply SO0; right; right; exists i; split; [exact Hi | reflexivity]).
  split.
  - apply (W_sok_blk C A1 Mi _ _ _ (v_rows v i + 4 * j) 4 CK HW Lr); rewrite u_Z2bv by lia; cbn; lia.
  - assert (WP : W C A1 (wbytes Mi (Z_to_bv 64 (v_rows v i + 4 * j)) (word_to_le_bytes 4 (Z_to_bv 64 ty))) md1 /\
                 POSTM C A s m (wbytes Mi (Z_to_bv 64 (v_rows v i + 4 * j)) (word_to_le_bytes 4 (Z_to_bv 64 ty))))
      by (apply (WP_blk C A A1 m Mi _ (Z_to_bv 64 (v_rows v i)) _ (4 * v_sx v) _ s CK (conj HW PM) Lr LrA Lr0 SUB); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia).
    split; [exact (proj1 WP)|]. split; [exact (proj2 WP)|]. split.
    + apply (sccells_frame Mi _ s); [lia | lia | exact CE |]. intros x Hx.
      apply wbytes_outside; rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia.
    + intros x Hx. rewrite wbytes_outside; [apply FR; exact Hx | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia |].
      rewrite length_N_to_le_bytes, u_Z2bv by lia. cbn. pose proof (Hx i Hi). lia.
Qed.

(* [comment removed for export] *)
Lemma brk_inner : forall (k : nat) C A A1 md1 m M1 Mi (s sel ty : Z) v regs r (i j : Z) (S : TSet),
  bctx C A A1 md1 M1 s sel v -> bst C A A1 md1 m M1 Mi s v regs -> (0 <= i < v_sy v)%Z -> (0 <= j < v_sx v)%Z -> (Z.of_nat k = v_sx v - 1 - j)%Z ->
  getr r 11 = Z_to_bv 64 ty -> getr r 17 = Z_to_bv 64 (v_rows v i) -> getr r 5 = Z_to_bv 64 1 -> getr r 6 = Z_to_bv 64 1 ->
  getr r 7 = Z_to_bv 64 (v_sx v - j) -> getr r 28 = Z_to_bv 64 (v_rows v i + 4 * j) -> getr r 29 = Z_to_bv 64 (v_rows v i + 4 * j) ->
  (forall M' r', bst C A A1 md1 m M1 M' s v regs -> regs_agree (fun x => In x [7; 28; 29; 30]%list) r r' ->
     realizes SEGS (mkCfg (mkst r' (0x27618 : word) M' al_rom) md1) S) ->
  realizes SEGS (mkCfg (mkst r (0x275f0 : word) Mi al_rom) md1) S.
Proof.
  induction k as [|k IH]; intros C A A1 md1 m M1 Mi s sel ty v regs r i j S BC BS Hi Hj Hk R11 R17 R5 R6 R7 R28 R29 HK;
    destruct (bst_store C A A1 md1 m M1 Mi s sel v regs i j ty BC BS Hi Hj) as [SOK BS'];
    pose proof BC as (CK & _ & _ & _ & _ & SA & _ & _ & _ & Hsx & _); pose proof SA as (_ & _ & _ & _ & _ & _ & _ & _ & ROWS & _);
    destruct (ROWS i Hi) as ((Gr & TOPr & _) & _); pose proof (alloc_top_lt (c_vm C)) as AT; unfold two_pow_64 in AT;
    pose proof BS as (HW & _).
  - destruct (bk_I_last al_rom r Mi (v_rows v i) (v_sx v) j ty ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SOK R11 R17 R5 R6 R7 R28 R29) as (r1 & RUN1 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
    exact (HK _ r1 BS' AG1).
  - destruct (bk_I_cont al_rom r Mi (v_rows v i) (v_sx v) j ty ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SOK R11 R17 R5 R6 R7 R28 R29)
      as (r1 & RUN1 & Q7 & Q28 & Q29 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
    apply (IH C A A1 md1 m M1 _ s sel ty v regs r1 i (j + 1)%Z S BC BS' Hi ltac:(lia) ltac:(lia)).
    + rewrite (AG1 11) by notin_lit. exact R11.
    + rewrite (AG1 17) by notin_lit. exact R17.
    + rewrite (AG1 5) by notin_lit. exact R5.
    + rewrite (AG1 6) by notin_lit. exact R6.
    + exact Q7.
    + exact Q28.
    + exact Q29.
    + intros M' r' B' AG'. apply (HK M' r' B'). exact (regs_agree_trans _ _ _ _ AG1 AG').
Qed.

#[local] Definition bk_rest : list (bv 5) := [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
Lemma brk_outer : forall (k : nat) C A A1 md1 m M1 Mi (s sel ty : Z) v regs r (i : Z) (S : TSet),
  bctx C A A1 md1 M1 s sel v -> bst C A A1 md1 m M1 Mi s v regs -> (0 <= i < v_sy v)%Z -> (Z.of_nat k = v_sy v - 1 - i)%Z -> ret_ok (getr regs 1) ->
  getr regs 2 = Z_to_bv 64 s -> getr r 2 = Z_to_bv 64 (s - 48) -> getr r 10 = Z_to_bv 64 sel -> getr r 11 = Z_to_bv 64 ty -> getr r 12 = Z_to_bv 64 (v_sy v) ->
  getr r 13 = Z_to_bv 64 i -> getr r 14 = Z_to_bv 64 (v_data v) -> getr r 15 = Z_to_bv 64 (v_sx v) -> getr r 16 = Z_to_bv 64 1 ->
  (forall x, In x bk_rest -> getr r x = getr regs x) ->
  (forall M' r', bst C A A1 md1 m M1 M' s v regs -> cs_kept regs r' -> getr r' 2 = Z_to_bv 64 s -> getr r' 10 = Z_to_bv 64 sel ->
     realizes SEGS (mkCfg (mkst r' (getr regs 1) M' al_rom) md1) S) ->
  realizes SEGS (mkCfg (mkst r (0x275b0 : word) Mi al_rom) md1) S.
Proof.
  induction k as [|k IH]; intros C A A1 md1 m M1 Mi s sel ty v regs r i S BC BS Hi Hk Hret H2 R2 R10 R11 R12 R13 R14 R15 R16 RR HK;
    pose proof BC as (CK & Hs16 & Hlo & Hhi & HW1 & SA1 & SO & SO0 & SUB & Hsx & Hsy);
    pose proof BS as (HW & PM & CE & FR);
    pose proof CK as [T1 T2 T3 T4 T5]; laypins; pose proof (alloc_top_lt (c_vm C)) as AT; unfold two_pow_64 in AT; unfold bk_rest in RR;
    pose proof (sel_at_rows_frame C A1 M1 md1 Mi (alloc_top (c_vm C)) sel v CK HW1 AT SA1 FR) as SAi;
    pose proof SAi as (_ & _ & _ & _ & _ & Bd & _ & _ & ROWS & _); pose proof Bd as (Gd & TOPd & _);
    destruct (ROWS i Hi) as (Br & _ & _ & _ & Bi); pose proof Br as (Gr & TOPr & _);
    pose proof (bytes_at_rdn SEGS Mi (v_data v + 8 * i) (Z_to_le_bytes 8 (v_rows v i)) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) Bi) as Rr; rewrite length_Z_to_le_bytes in Rr;
    destruct (bk_O al_rom r Mi (v_data v) i (v_rows v i) (v_sx v) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (bok_mod8 _ _ _ Bd) (bok_mod4 _ _ _ Br) Rr R13 R14 R15 R16)
      as (r1 & RUN1 & Q17 & Q5 & Q6 & Q7 & Q28 & Q29 & AG1);
    (eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]);
    assert (E11' : getr r1 11 = Z_to_bv 64 ty) by (rewrite (AG1 11) by notin_lit; exact R11);
    assert (E7' : getr r1 7 = Z_to_bv 64 (v_sx v - 0)) by (rewrite Q7; f_equal; lia);
    assert (E28' : getr r1 28 = Z_to_bv 64 (v_rows v i + 4 * 0)) by (rewrite Q28; f_equal; lia);
    assert (E29' : getr r1 29 = Z_to_bv 64 (v_rows v i + 4 * 0)) by (rewrite Q29; f_equal; lia);
    apply (brk_inner (Z.to_nat (v_sx v - 1)) C A A1 md1 m M1 Mi s sel ty v regs r1 i 0 S BC BS Hi ltac:(lia) ltac:(lia) E11' Q17 Q5 Q6 E7' E28' E29');
    intros M' r2 BS' AG2; pose proof BS' as (HW' & PM' & CE' & FR');
    assert (E13 : getr r2 13 = Z_to_bv 64 i) by (rewrite (AG2 13) by notin_lit; rewrite (AG1 13) by notin_lit; exact R13);
    assert (E12 : getr r2 12 = Z_to_bv 64 (v_sy v)) by (rewrite (AG2 12) by notin_lit; rewrite (AG1 12) by notin_lit; exact R12).
  - (* [comment removed for export] *)
    assert (E2 : getr r2 2 = Z_to_bv 64 (s - 48)) by (rewrite (AG2 2) by notin_lit; rewrite (AG1 2) by notin_lit; exact R2).
    destruct (bk_N_last al_rom r2 M' s i (v_sy v) (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hret CE' E2 E13 E12) as (r3 & RUN3 & P2 & P1 & P10 & P8 & P9 & P18 & P19 & P20 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN3 |].
    apply (HK M' r3 BS').
    + assert (REST : forall x, In x bk_rest -> getr r3 x = getr regs x).
      { intros x Hx. unfold bk_rest in Hx. cbn [In] in Hx.
        repeat (destruct Hx as [<-|Hx];
                [rewrite (AG3 _) by notin_lit; rewrite (AG2 _) by notin_lit;
                 rewrite (AG1 _) by notin_lit; apply RR; in_lit|]). destruct Hx. }
      apply cs_kept_intro; first [ rewrite P2; symmetry; exact H2 | exact P8 | exact P9 | exact P18 | exact P19 | exact P20 | apply REST; unfold bk_rest; in_lit ].
    + exact P2.
    + rewrite P10. rewrite (AG2 10) by notin_lit. rewrite (AG1 10) by notin_lit. exact R10.
  - (* [comment removed for export] *)
    destruct (bk_N_cont al_rom r2 M' i (v_sy v) ltac:(lia) ltac:(lia) ltac:(lia) E13 E12) as (r3 & RUN3 & P13 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN3 |].
    apply (IH C A A1 md1 m M1 M' s sel ty v regs r3 (i + 1)%Z S BC BS' ltac:(lia) ltac:(lia) Hret H2); try exact HK; try exact P13;
      try (rewrite (AG3 _) by notin_lit; rewrite (AG2 _) by notin_lit; rewrite (AG1 _) by notin_lit; assumption).
    intros x Hx. rewrite (AG3 x), (AG2 x), (AG1 x); [apply RR; exact Hx | | |]; cbn [In] in *; intros HH;
      repeat (destruct Hx as [<-|Hx]; [repeat (destruct HH as [HH|HH]; [apply (f_equal bv_unsigned) in HH; cbv in HH; discriminate HH|]); exact HH|]); exact Hx.
Qed.

(* [comment removed for export] *)
Lemma sel_at_set_cyx : forall C A m md sel sy sx arr rows cy cx, Cok C -> W C A m md ->
  (0 <= cy < 2 ^ 31)%Z -> (0 <= cx < 2 ^ 31)%Z ->
  sel_at (alloc_top (c_vm C)) A m sel (SELV sy sx 0 0 arr 0 rows) ->
  sel_at (alloc_top (c_vm C)) A (wbytes (wbytes m (Z_to_bv 64 (sel + 8)) (word_to_le_bytes 4 (Z_to_bv 64 cy)))
                                      (Z_to_bv 64 (sel + 12)) (word_to_le_bytes 4 (Z_to_bv 64 cx))) sel (SELV sy sx cy cx arr 0 rows).
Proof.
  intros C A m md sel sy sx arr rows cy cx CK HW Hcy Hcx (Hsy & Hsx & Bs & Ls & Rs & Bd & Ld & NEd & ROWS & DIST).
  cbn [v_sy v_sx v_cy v_cx v_data v_name v_rows] in *.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  destruct Bs as (Gs & TOPs & ALs). destruct Bd as (Gd & TOPd & ALd).
  pose proof (live_apart C A m md _ _ _ _ CK HW Ls Ld ltac:(apply zbv_ne; lia) ltac:(lia) ltac:(lia)) as AP. rewrite !u_Z2bv in AP by lia.
  unfold sel_at. cbn [v_sy v_sx v_cy v_cx v_data v_name v_rows].
  split; [exact Hsy|]. split; [exact Hsx|]. split; [exact (conj Gs (conj TOPs ALs))|]. split; [exact Ls|].
  split.
  { unfold sel_flds.
    eapply (REC_wr' _ _ [(4%nat, sy); (4%nat, sx); (4%nat, cy); (4%nat, 0%Z); (8%nat, arr); (8%nat, 0%Z)] _ 3 4);
      [ | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity ].
    eapply (REC_wr' _ _ [(4%nat, sy); (4%nat, sx); (4%nat, 0%Z); (4%nat, 0%Z); (8%nat, arr); (8%nat, 0%Z)] _ 2 4);
      [ exact Rs | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity ]. }
  split; [exact (conj Gd (conj TOPd ALd))|]. split; [exact Ld|]. split; [exact NEd|]. split; [|exact DIST].
  intros i Hi. destruct (ROWS i Hi) as (Br & Lr & N1 & N2 & Bi). do 4 (split; [assumption|]).
  apply bytes_at_wbytes_out; [| lia | rewrite length_Z_to_le_bytes; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia
                              | rewrite length_Z_to_le_bytes, length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
  apply bytes_at_wbytes_out; [exact Bi | lia | rewrite length_Z_to_le_bytes; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia
                              | rewrite length_Z_to_le_bytes, length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
Qed.

Theorem selCreateBrick_W : forall C A m md regs (s h w cy cx ty : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + 48 + 64 + CALLOC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x45480 ->
  getr regs 10 = Z_to_bv 64 h -> getr regs 11 = Z_to_bv 64 w -> getr regs 12 = Z_to_bv 64 cy -> getr regs 13 = Z_to_bv 64 cx -> getr regs 14 = Z_to_bv 64 ty ->
  (1 <= w <= 500)%Z -> (1 <= h <= 250)%Z -> (0 <= ty <= 2)%Z -> (0 <= cy < 2 ^ 31)%Z -> (0 <= cx < 2 ^ 31)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (2 + h <= kR)%Z -> ((2 + h) * RB10_small <= bR)%Z ->
  (forall A' m' vm' regs' (sel arr : Z) (rows : Z -> Z), W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 sel ->
     sel_at (alloc_top (c_vm C)) A' m' sel (SELV h w cy cx arr 0 rows) ->
     sel_off A sel (SELV h w cy cx arr 0 rows) -> sel_off (c_A0 C) sel (SELV h w cy cx arr 0 rows) -> sel_only A A' sel (SELV h w cy cx arr 0 rows) ->
     aroom A' vm' (kR - (2 + h)) (bR - (2 + h) * RB10_small) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x274cc : word) m al_rom) md) S.
Proof.
  intros C A m md regs s h w cy cx ty ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 H13 H14 Hw Hh Hty Hcy Hcx kR bR HRM HRK HRB HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  assert (HsS : (c_top C - LSTK + 96 <= s)%Z) by (unfold CALLOC_STACK, ALLOC_STACK in Hlo; lia).
  destruct (bk_A al_rom regs m s h w cy cx ty ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hty
              (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11 H12 H13 H14)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q8 & Q9 & Q18 & Q19 & Q20 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := SCF m s ret regs).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold SCF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (sccells_SCF m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1. rewrite <- H1 in CE1.
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x45480) by (rewrite (AG1 4) by notin_lit; exact H4).
  apply (selCreate_W C A M1 md r1 (s - 48) h w (Z_to_bv 64 0x2757c) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 Q11 Q12 Hw Hh kR bR HRM HRK HRB).
  intros A1 m1 vm1 r2 sel arr rows HWa CSa PMa Ra10 SAa SOa SO0a SNa HRMa.
  replace (Z_to_bv 64 0x2757c) with (0x2757c : word) by (apply bv_eq; reflexivity).
  pose proof SAa as (_ & _ & (Gs & TOPs & ALs) & Ls & Rs & (Gd & TOPd & ALd) & Ld & NEd & ROWSa & DISTa). cbn [v_sy v_sx v_cy v_cx v_data v_name v_rows] in *.
  pose proof (sccells_FRM C M1 m1 s _ _ _ _ _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) CE1) as CEa.
  assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  assert (SUBa : sub_live A A1).
  { intros q kq Lq. rewrite (SNa q); [exact Lq|]. intros p Hp ->. rewrite (SOa p Hp) in Lq. discriminate. }
  pose proof (REC_rd' SEGS m1 sel _ 4 8 (Z_to_bv 64 (sel + 16)) arr Rs ltac:(cbn; lia) eq_refl eq_refl eq_refl) as Rdata.
  assert (E18 : getr r2 18 = Z_to_bv 64 cy) by (rewrite (CSa 18%bv cs18); exact Q18).
  assert (E9 : getr r2 9 = Z_to_bv 64 cx) by (rewrite (CSa 9%bv cs9); exact Q9).
  assert (E8 : getr r2 8 = Z_to_bv 64 ty) by (rewrite (CSa 8%bv cs8); exact Q8).
  assert (E19 : getr r2 19 = Z_to_bv 64 h) by (rewrite (CSa 19%bv cs19); exact Q19).
  assert (E20 : getr r2 20 = Z_to_bv 64 w) by (rewrite (CSa 20%bv cs20); exact Q20).
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 48)) by (rewrite (CSa 2%bv cs2); exact Q2).
  destruct (bk_B al_rom r2 m1 sel arr h w cy cx ty ltac:(lia) ltac:(lia) (bok_mod8 _ _ _ (conj Gs (conj TOPs ALs))) ltac:(lia) ltac:(lia) ltac:(lia) Rdata
              (W_sok_blk C A1 m1 _ _ _ (sel + 8) 8 CK HWa Ls ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; cbn; lia) ltac:(rewrite u_Z2bv by lia; lia))
              Ra10 E18 E9 E8 E19 E20) as (r3 & RUN3 & P10 & P11 & P12 & P13 & P14 & P15 & P16a & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
  set (M2 := wbytes (wbytes m1 _ _) _ _).
  assert (LsA : live A (Z_to_bv 64 sel) = None) by (apply SOa; left; reflexivity).
  assert (Ls0 : live (c_A0 C) (Z_to_bv 64 sel) = None) by (apply SO0a; left; reflexivity).
  assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A s m M2).
  { subst M2.
    do 2 (apply (WP_blk C A A1 m _ _ (Z_to_bv 64 sel) _ 32); [exact CK | | exact Ls | exact LsA | exact Ls0 | exact SUBa | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]).
    split; [exact HWa | exact PMa']. }
  destruct WP2 as [HW2 PM2].
  pose proof (sel_at_set_cyx C A1 m1 _ sel h w arr rows cy cx CK HWa Hcy Hcx SAa) as SA2. fold M2 in SA2.
  assert (CE2 : sccells M2 s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)).
  { apply (sccells_frame m1 M2 s); [lia | lia | exact CEa |]. intros x Hx. subst M2.
    rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  set (v := SELV h w cy cx arr 0 rows) in *.
  assert (BC : bctx C A A1 (with_vmmaps vm1 md) M2 s sel v).
  { split; [exact CK|]. split; [exact Hs16|]. split; [lia|]. split; [exact Hhi|]. split; [exact HW2|]. split; [exact SA2|].
    split; [exact SOa|]. split; [exact SO0a|]. split; [exact SUBa|]. cbn [v_sx v_sy v]. lia. }
  assert (BS : bst C A A1 (with_vmmaps vm1 md) m M2 M2 s v regs).
  { split; [exact HW2|]. split; [exact PM2|]. split; [exact CE2|]. intros x _. reflexivity. }
  apply (brk_outer (Z.to_nat (h - 1)) C A A1 (with_vmmaps vm1 md) m M2 M2 s sel ty v regs r3 0 S BC BS); cbn [v_sy v_sx v_data v]; try lia.
  - rewrite H1. exact Hret.
  - exact H2.
  - rewrite (AG3 2) by notin_lit. exact E2.
  - exact P10.
  - exact P11.
  - exact P12.
  - exact P13.
  - exact P14.
  - exact P15.
  - exact P16a.
  - intros x Hx. rewrite (AG3 x).
    + unfold bk_rest in Hx. cbn [In] in Hx.
      repeat (destruct Hx as [<-|Hx]; [first [ rewrite (CSa _ cs3) | rewrite (CSa _ cs4) | rewrite (CSa _ cs21) | rewrite (CSa _ cs22) | rewrite (CSa _ cs23)
                                              | rewrite (CSa _ cs24) | rewrite (CSa _ cs25) | rewrite (CSa _ cs26) | rewrite (CSa _ cs27) ];
                                       rewrite (AG1 _) by notin_lit; reflexivity|]). destruct Hx.
    + unfold bk_rest in Hx. cbn [In] in *. intros HH.
      repeat (destruct Hx as [<-|Hx]; [repeat (destruct HH as [HH|HH]; [apply (f_equal bv_unsigned) in HH; cbv in HH; discriminate HH|]); exact HH|]); exact Hx.
  - (* [comment removed for export] *)
    intros M' r' (HW' & PM' & CE' & FR') CS' R2' R10'. rewrite H1.
    apply (HK A1 M' vm1 r' sel arr rows HW' CS' PM' R10').
    + exact (sel_at_rows_frame C A1 M2 _ M' (alloc_top (c_vm C)) sel v CK HW2 AT SA2 FR').
    + exact SOa.
    + exact SO0a.
    + exact SNa.
    + exact HRMa.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SegsE.
Variable rom : word -> option byte.

  Lemma sse_run : forall regs m (sel sy sx data rowp row col ty : Z) (ret : word),
    (1 <= sel)%Z -> (sel + 32 < 2 ^ 64)%Z -> (0 <= row < sy)%Z -> (0 <= col < sx)%Z -> (sy < 2 ^ 31)%Z -> (sx < 2 ^ 31)%Z -> (0 <= ty <= 2)%Z ->
    (1 <= data)%Z -> (data + 8 * sy < 2 ^ 64)%Z -> (1 <= rowp)%Z -> (rowp + 4 * sx < 2 ^ 64)%Z ->
    (sel mod 8 = 0)%Z -> (data mod 8 = 0)%Z -> (rowp mod 4 = 0)%Z ->
    rdn SEGS m (Z_to_bv 64 sel) 4 = Some (Z_to_le_bytes 4 sy) -> rdn SEGS m (Z_to_bv 64 (sel + 4)) 4 = Some (Z_to_le_bytes 4 sx) ->
    rdn SEGS m (Z_to_bv 64 (sel + 16)) 8 = Some (Z_to_le_bytes 8 data) -> rdn SEGS m (Z_to_bv 64 (data + 8 * row)) 8 = Some (Z_to_le_bytes 8 rowp) ->
    store_ok SEGS m (Z_to_bv 64 (rowp + 4 * col)) 4 = true ->
    getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 sel -> getr regs 11 = Z_to_bv 64 row -> getr regs 12 = Z_to_bv 64 col -> getr regs 13 = Z_to_bv 64 ty ->
    exists regs',
      msteps SEGS (mkst regs (0x2766c : word) m rom)
                  (mkst regs' ret (wbytes m (Z_to_bv 64 (rowp + 4 * col)) (word_to_le_bytes 4 (Z_to_bv 64 ty))) rom)
      /\ getr regs' 10 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [10; 11; 12; 14; 15]%list) regs regs'.
  Proof.
    intros regs m sel sy sx data rowp row col ty ret Hs Hs64 Hrow Hcol Hsy Hsx Hty Hd Hd64 Hr Hr64 ALs ALd ALr Rsy Rsx Rd Rr SOK H1 Hret H10 H11 H12 H13.
    assert (ALc : ((data + 8 * row) mod 8 = 0)%Z) by (rewrite Z.mul_comm, Z_mod_plus_full; exact ALd).
    assert (ALe : ((rowp + 4 * col) mod 4 = 0)%Z) by (rewrite Z.mul_comm, Z_mod_plus_full; exact ALr).
    eexists. split.
    - stepb_ft F_27570 D_27570 ltac:(condZ).
      sn F_27574 D_27574.
      stepb_tk F_27578 D_27578 ltac:(condZ).
      stepb_ft F_275d4 D_275d4 ltac:(condZ).
      zand F_275d8 D_275d8 andi_7 ALs. stepb_ft F_275dc D_275dc ltac:(condZ).          (* [comment removed for export] *)
      stepLD F_275e0 D_275e0 (Z_to_le_bytes 4 sy) (Z_to_bv 64 sy) ltac:(addr_norm; exact Rsy) ltac:(apply lez4; lia).
      rewrite (v_lw_small sy) by lia.
      stepb_ft F_275e4 D_275e4 ltac:(condZ).
      stepb_ft F_275e8 D_275e8 ltac:(condZ).
      stepLD F_275ec D_275ec (Z_to_le_bytes 4 sx) (Z_to_bv 64 sx) ltac:(addr_norm; exact Rsx) ltac:(apply lez4; lia).
      rewrite (v_lw_small sx) by lia.
      stepb_ft F_275f0 D_275f0 ltac:(condZ).
      stepLD F_275f4 D_275f4 (Z_to_le_bytes 8 data) (Z_to_bv 64 data) ltac:(addr_norm; exact Rd) ltac:(apply lez8; lia).
      stepiv F_275f8 D_275f8 (Z_to_bv 64 (8 * row)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; lia).
      zv F_275fc D_275fc (Z_to_bv 64 (data + 8 * row)).
      stepb_ft F_27600 D_27600 ltac:(condZ).                                          (* [comment removed for export] *)
      snez1 F_27604 D_27604.                                                          (* [comment removed for export] *)
      seqz0 F_27608 D_27608.                                                          (* [comment removed for export] *)
      zlit F_2760c D_2760c (Z_to_bv 64 1).                                            (* [comment removed for export] *)
      stepb_ft F_27610 D_27610 ltac:(condZ).                                          (* [comment removed for export] *)
      stepb_ft F_27614 D_27614 ltac:(condZ).                                          (* [comment removed for export] *)
      zand F_27618 D_27618 andi_7 ALc. stepb_ft F_2761c D_2761c ltac:(condZ).          (* [comment removed for export] *)
      stepLD F_27620 D_27620 (Z_to_le_bytes 8 rowp) (Z_to_bv 64 rowp) ltac:(addr_norm; exact Rr) ltac:(apply lez8; lia).
      stepiv F_27624 D_27624 (Z_to_bv 64 (4 * col)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; lia).
      zv F_27628 D_27628 (Z_to_bv 64 (rowp + 4 * col)).
      stepb_ft F_2762c D_2762c ltac:(condZ).                                          (* [comment removed for export] *)
      snez1 F_27630 D_27630.                                                          (* [comment removed for export] *)
      seqz0 F_27634 D_27634.                                                          (* [comment removed for export] *)
      zlit F_27638 D_27638 (Z_to_bv 64 1).                                            (* [comment removed for export] *)
      stepb_ft F_2763c D_2763c ltac:(condZ).                                          (* [comment removed for export] *)
      stepb_ft F_27640 D_27640 ltac:(condZ).                                          (* [comment removed for export] *)
      zand F_27644 D_27644 andi_3 ALe. stepb_ft F_27648 D_27648 ltac:(condZ).          (* [comment removed for export] *)
      stepST F_2764c D_2764c (Z_to_bv 64 (rowp + 4 * col)) (Z_to_bv 64 ty) ltac:(store_ok_peel; exact SOK).
      stepret F_27650 D_27650 ret ltac:(exact H1).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End SegsE.

(* [comment removed for export] *)
Theorem selSetElement_W : forall C Ar A m mb md regs (s sel row col ty : Z) (v : selv) (ret : word) (S : TSet),
  Cok C -> W C A m md -> POSTM C Ar s mb m -> sub_live Ar A -> (s <= c_top C)%Z ->
  sel_at (alloc_top (c_vm C)) A m sel v -> sel_off Ar sel v -> sel_off (c_A0 C) sel v ->
  (0 <= row < v_sy v)%Z -> (0 <= col < v_sx v)%Z -> (0 <= ty <= 2)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 sel -> getr regs 11 = Z_to_bv 64 row -> getr regs 12 = Z_to_bv 64 col -> getr regs 13 = Z_to_bv 64 ty ->
  (forall m' regs', W C A m' md -> POSTM C Ar s mb m' -> sel_at (alloc_top (c_vm C)) A m' sel v ->
     (forall x : word, outside_rows v x -> m' x = m x) ->
     regs_agree (fun r => In r [10; 11; 12; 14; 15]%list) regs regs' -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x2766c : word) m al_rom) md) S.
Proof.
  intros C Ar A m mb md regs s sel row col ty v ret S CK HW PM SUB Hs SA SO SO0 Hrow Hcol Hty H1 Hret H10 H11 H12 H13 HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  pose proof SA as (Hsy & Hsx & (Gs & TOPs & ALs) & Ls & Rs & (Gd & TOPd & ALd) & Ld & NEd & ROWS & DIST).
  destruct (ROWS row Hrow) as ((Gr & TOPr & ALr) & Lr & _ & _ & Bi).
  pose proof (REC_rd' SEGS m sel _ 0 4 (Z_to_bv 64 sel) (v_sy v) Rs ltac:(cbn; lia) eq_refl ltac:(cbn [fld_off sel_flds Z.of_nat]; f_equal; lia) eq_refl) as Rsy.
  pose proof (REC_rd' SEGS m sel _ 1 4 (Z_to_bv 64 (sel + 4)) (v_sx v) Rs ltac:(cbn; lia) eq_refl eq_refl eq_refl) as Rsx.
  pose proof (REC_rd' SEGS m sel _ 4 8 (Z_to_bv 64 (sel + 16)) (v_data v) Rs ltac:(cbn; lia) eq_refl eq_refl eq_refl) as Rd.
  pose proof (bytes_at_rdn SEGS m (v_data v + 8 * row) (Z_to_le_bytes 8 (v_rows v row)) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) Bi) as Rr.
  rewrite length_Z_to_le_bytes in Rr.
  assert (LrA : live Ar (Z_to_bv 64 (v_rows v row)) = None) by (apply SO; right; right; exists row; split; [exact Hrow | reflexivity]).
  assert (Lr0 : live (c_A0 C) (Z_to_bv 64 (v_rows v row)) = None) by (apply SO0; right; right; exists row; split; [exact Hrow | reflexivity]).
  destruct (sse_run al_rom regs m sel (v_sy v) (v_sx v) (v_data v) (v_rows v row) row col ty ret ltac:(lia) ltac:(lia) Hrow Hcol ltac:(lia) ltac:(lia) Hty
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              (bok_mod8 _ _ _ (conj Gs (conj TOPs ALs))) (bok_mod8 _ _ _ (conj Gd (conj TOPd ALd))) (bok_mod4 _ _ _ (conj Gr (conj TOPr ALr))) Rsy Rsx Rd Rr
              (W_sok_blk C A m _ _ _ (v_rows v row + 4 * col) 4 CK HW Lr ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; cbn; lia) ltac:(rewrite u_Z2bv by lia; lia))
              H1 Hret H10 H11 H12 H13) as (r1 & RUN1 & Q10 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M' := wbytes m _ _).
  assert (WP : W C A M' md /\ POSTM C Ar s mb M')
    by (subst M'; apply (WP_blk C Ar A mb m _ (Z_to_bv 64 (v_rows v row)) _ (4 * v_sx v) _ s CK (conj HW PM) Lr LrA Lr0 SUB); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia).
  assert (FR : forall x : word, outside_rows v x -> M' x = m x).
  { intros x Hx. subst M'. apply wbytes_outside; rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; [lia|]. pose proof (Hx row Hrow). lia. }
  apply (HK M' r1 (proj1 WP) (proj2 WP)); [| exact FR | exact AG1 | exact Q10].
  exact (sel_at_rows_frame C A m md M' (alloc_top (c_vm C)) sel v CK HW AT SA FR).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SegsS.
Variable rom : word -> option byte.

  Definition AAF (m : word -> option byte) (s sel : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
      (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
      (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
      (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
      (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (Z_to_bv 64 sel)).

  (* [comment removed for export] *)
  Lemma as_A : forall regs m (s sela sel nm : Z) (ret : word),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= sela < 2 ^ 64)%Z -> (1 <= sel)%Z -> (sel + 32 < 2 ^ 64)%Z -> (1 <= nm < 2 ^ 64)%Z ->
    (sel + 32 <= s - 64 \/ s <= sel)%Z -> (sel mod 8 = 0)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true ->
    rdn SEGS m (Z_to_bv 64 (sel + 24)) 8 = Some (Z_to_le_bytes 8 0) ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 sela -> getr regs 11 = Z_to_bv 64 sel ->
    getr regs 12 = Z_to_bv 64 nm -> getr regs 13 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x277b4 : word) m rom) (mkst regs' (0x158d0 : word) (AAF m s sel ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 1 = Z_to_bv 64 0x27914 /\ getr regs' 10 = Z_to_bv 64 nm
      /\ getr regs' 8 = Z_to_bv 64 sela /\ getr regs' 9 = Z_to_bv 64 sel /\ getr regs' 18 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 14; 15; 18]%list) regs regs'.
  Proof.
    intros regs m s sela sel nm ret Hs Hs64 Hsela Hsel Hsel64 Hnm DJ ALs SOK Rname H2 H1 H10 H11 H12 H13.
    eexists. split.
    - zv F_276b8 D_276b8 (Z_to_bv 64 (s - 64)).
      stepST F_276bc D_276bc (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_276c0 D_276c0 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_276c4 D_276c4 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_276c8 D_276c8 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_276cc D_276cc (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_276d0 D_276d0 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepb_ft F_276d4 D_276d4 ltac:(condZ).
      stepb_ft F_276d8 D_276d8 ltac:(condZ).
      zand F_276dc D_276dc andi_7 ALs. stepb_ft F_276e0 D_276e0 ltac:(condZ).          (* [comment removed for export] *)
      stepLD F_276e4 D_276e4 (Z_to_le_bytes 8 0) (Z_to_bv 64 0) ltac:(addr_norm; repeat rdn_peel1; exact Rname) ltac:(apply lez8; lia).
      sn F_276e8 D_276e8. fixv (Z_to_bv 64 nm) ltac:(pin; unfold v_or; rewrite !u_Z2bv by lia; rewrite Z.lor_0_r; reflexivity).
      stepb_ft F_276ec D_276ec ltac:(condZ).
      sn F_276f0 D_276f0.
      stepb_tk F_276f4 D_276f4 ltac:(condZ).
      sn F_277b8 D_277b8.
      stepb_tk F_277bc D_277bc ltac:(condZ).
      stepST F_277f0 D_277f0 (Z_to_bv 64 (s - 56)) (Z_to_bv 64 sel) ltac:(sok_in SOK).
      zand F_277f4 D_277f4 andi_7 ALs. stepb_ft F_277f8 D_277f8 ltac:(condZ).          (* [comment removed for export] *)
      stepLD F_277fc D_277fc (Z_to_le_bytes 8 0) (Z_to_bv 64 0) ltac:(addr_norm; repeat rdn_peel1; exact Rname) ltac:(apply lez8; lia).
      stepb_ft F_27800 D_27800 ltac:(condZ).
      sn F_27804 D_27804. sn F_27808 D_27808. sn F_2780c D_2780c. sn F_27810 D_27810. sn F_27814 D_27814.
      unfold AAF. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Definition aacells (M : word -> option byte) (s : Z) (ret s0v s1v s2v s3v s4v : word) : Prop :=
    rdn SEGS M (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
    rdn SEGS M (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
    rdn SEGS M (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) /\
    rdn SEGS M (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) /\
    rdn SEGS M (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v) /\
    rdn SEGS M (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 s4v).

  Lemma aacells_AAF : forall m s sel ret regs, (64 <= s)%Z -> (s < 2 ^ 64)%Z ->
    aacells (AAF m s sel ret regs) s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20).
  Proof. intros m s sel ret regs Hs Hs64. unfold aacells, AAF. repeat split; rdn_chain. Qed.

  (* [comment removed for export] *)
  Lemma as_B : forall regs m (s sela sel arr n name : Z) (ret s0v s1v s2v s3v s4v : word),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= sela)%Z -> (sela + 16 <= s - 64)%Z -> (1 <= sel)%Z -> (sel + 32 <= s - 64)%Z ->
    (1 <= arr)%Z -> (arr + 400 <= s - 64)%Z -> (0 <= n < 50)%Z -> (0 <= name < 2 ^ 64)%Z ->
    (sela + 16 <= sel \/ sel + 32 <= sela)%Z -> (sela + 16 <= arr \/ arr + 400 <= sela)%Z -> (sel + 32 <= arr \/ arr + 400 <= sel)%Z ->
    (sela mod 8 = 0)%Z -> (arr mod 8 = 0)%Z ->
    rdn SEGS m (Z_to_bv 64 sela) 4 = Some (Z_to_le_bytes 4 n) -> rdn SEGS m (Z_to_bv 64 (sela + 4)) 4 = Some (Z_to_le_bytes 4 50) ->
    rdn SEGS m (Z_to_bv 64 (sela + 8)) 8 = Some (Z_to_le_bytes 8 arr) ->
    store_ok SEGS m (Z_to_bv 64 (sel + 24)) 8 = true -> store_ok SEGS m (Z_to_bv 64 (arr + 8 * n)) 8 = true -> store_ok SEGS m (Z_to_bv 64 sela) 4 = true ->
    ret_ok ret -> aacells m s ret s0v s1v s2v s3v s4v ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 10 = Z_to_bv 64 name -> getr regs 8 = Z_to_bv 64 sela -> getr regs 9 = Z_to_bv 64 sel -> getr regs 18 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x27914 : word) m rom)
                  (mkst regs' ret (wbytes (wbytes (wbytes m (Z_to_bv 64 (sel + 24)) (word_to_le_bytes 8 (Z_to_bv 64 name)))
                                                  (Z_to_bv 64 (arr + 8 * n)) (word_to_le_bytes 8 (Z_to_bv 64 sel)))
                                          (Z_to_bv 64 sela) (word_to_le_bytes 4 (Z_to_bv 64 (n + 1)))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 18; 19; 20]%list) regs regs'.
  Proof.
    intros regs m s sela sel arr n name ret s0v s1v s2v s3v s4v Hs Hs64 Hsela Hsela2 Hsel Hsel2 Harr Harr2 Hn Hname D1 D2 D3 ALsa ALar Rn Rna Rarr SOK1 SOK2 SOK3 Hret CE H2 H10 H8 H9 H18.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6).
    assert (ALc : ((arr + 8 * n) mod 8 = 0)%Z) by (rewrite Z.mul_comm, Z_mod_plus_full; exact ALar).
    eexists. split.
    - sn F_27818 D_27818. sn F_2781c D_2781c. sn F_27820 D_27820. sn F_27824 D_27824.
      stepST F_27828 D_27828 (Z_to_bv 64 (sel + 24)) (Z_to_bv 64 name) ltac:(store_ok_peel; exact SOK1).
      zand F_2782c D_2782c andi_7 ALsa. stepb_ft F_27830 D_27830 ltac:(condZ).         (* [comment removed for export] *)
      stepLD F_27834 D_27834 (Z_to_le_bytes 4 n) (Z_to_bv 64 n) ltac:(addr_norm; repeat rdn_peel1; exact Rn) ltac:(apply lez4; lia).
      rewrite (v_lw_small n) by lia.
      stepLD F_27838 D_27838 (Z_to_le_bytes 4 50) (Z_to_bv 64 50) ltac:(addr_norm; repeat rdn_peel1; exact Rna) ltac:(apply lez4; lia).
      rewrite ?(v_lw_small 50) by lia.
      stepb_tk F_2783c D_2783c ltac:(condZ).
      stepLD F_27888 D_27888 (Z_to_le_bytes 8 arr) (Z_to_bv 64 arr) ltac:(addr_norm; repeat rdn_peel1; exact Rarr) ltac:(apply lez8; lia).
      stepiv F_2788c D_2788c (Z_to_bv 64 (8 * n)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; lia).
      zv F_27890 D_27890 (Z_to_bv 64 (arr + 8 * n)).
      snez1 F_27894 D_27894.                                                          (* [comment removed for export] *)
      seqz0 F_27898 D_27898.                                                          (* [comment removed for export] *)
      stepb_ft F_2789c D_2789c ltac:(condR).                                          (* [comment removed for export] *)
      sltu0' F_278a0 D_278a0.                                                         (* [comment removed for export] *)
      slti0' F_278a4 D_278a4.                                                         (* [comment removed for export] *)
      sn F_278a8 D_278a8. sn F_278ac D_278ac.                                         (* [comment removed for export] *)
      stepb_ft F_278b0 D_278b0 ltac:(condR).                                          (* [comment removed for export] *)
      stepb_ft F_278b4 D_278b4 ltac:(condZ).                                          (* [comment removed for export] *)
      zand F_278b8 D_278b8 andi_7 ALc. stepb_ft F_278bc D_278bc ltac:(condZ).          (* [comment removed for export] *)
      stepLD F_278c0 D_278c0 (Z_to_le_bytes 4 n) (Z_to_bv 64 n) ltac:(addr_norm; repeat rdn_peel1; exact Rn) ltac:(apply lez4; lia).
      rewrite (v_lw_small n) by lia.
      sn F_278c4 D_278c4. fixv (Z_to_bv 64 (n + 1)) ltac:(pin; rewrite zbv_addiw_small by lia; reflexivity).   (* [comment removed for export] *)
      stepST F_278c8 D_278c8 (Z_to_bv 64 (arr + 8 * n)) (Z_to_bv 64 sel) ltac:(store_ok_peel; exact SOK2).
      stepb_ft F_278cc D_278cc ltac:(condZ).                                          (* [comment removed for export] *)
      stepST F_278d0 D_278d0 (Z_to_bv 64 sela) (Z_to_bv 64 (n + 1)) ltac:(store_ok_peel; exact SOK3).
      sn F_278d4 D_278d4. sn F_278d8 D_278d8.
      stepLD8 F_27980 D_27980 ret. stepLD8 F_27984 D_27984 s0v. stepLD8 F_27988 D_27988 s1v.
      stepLD8 F_2798c D_2798c s2v. stepLD8 F_27990 D_27990 s3v. stepLD8 F_27994 D_27994 s4v.
      zv F_27998 D_27998 (Z_to_bv 64 s).
      stepret F_2799c D_2799c ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End SegsS.

Lemma aacells_FRM : forall C M M' s ret s0v s1v s2v s3v s4v, Cok C -> FRM C (s - 64) M M' ->
  (c_top C - LSTK <= s - 64)%Z -> (s <= c_top C)%Z ->
  aacells M s ret s0v s1v s2v s3v s4v -> aacells M' s ret s0v s1v s2v s3v s4v.
Proof.
  intros C M M' s ret s0v s1v s2v s3v s4v CK F Hlo Hhi (C1 & C2 & C3 & C4 & C5 & C6).
  pose proof CK as [T1 T2 T3 T4 T5]. unfold aacells.
  rewrite !(FRM_rdn16 C (s - 64) M M' _ _ CK F) by lia. repeat split; assumption.
Qed.

#[local] Definition aa_rest : list (bv 5) := [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
Theorem selaAddSel_W : forall C Ar A m md regs (s sela arr k sel src p : Z) (sels : Z -> Z) (vs : Z -> selv) (nms : Z -> list byte) (v : selv)
                              (bs wd : list byte) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 64 + 32 + CALLOC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x45480 ->
  getr regs 10 = Z_to_bv 64 sela -> getr regs 11 = Z_to_bv 64 sel -> getr regs 12 = Z_to_bv 64 src -> getr regs 13 = Z_to_bv 64 0 ->
  sela_at (alloc_top (c_vm C)) A m sela arr k sels vs nms -> (0 <= k < 50)%Z ->
  sel_at (alloc_top (c_vm C)) A m sel v -> v_name v = 0%Z ->
  live Ar (Z_to_bv 64 sela) = None -> live Ar (Z_to_bv 64 arr) = None -> live Ar (Z_to_bv 64 sel) = None ->
  live (c_A0 C) (Z_to_bv 64 sela) = None -> live (c_A0 C) (Z_to_bv 64 arr) = None -> live (c_A0 C) (Z_to_bv 64 sel) = None ->
  (forall q, sel_blk sel v q -> q <> sela /\ q <> arr /\ forall i p', (0 <= i < k)%Z -> seln_blk (sels i) (vs i) p' -> p' <> q) ->
  (0x10000 <= src)%Z -> (src + Z.of_nat (length bs) + 16 <= 0x2b000)%Z -> (1 <= Z.of_nat (length bs) <= 2027)%Z ->
  rdn SEGS (fun _ => None) (Z_to_bv 64 src) (Datatypes.S (length bs)) = Some (bs ++ [Z_to_bv 8 0]) -> Forall (fun b => b <> Z_to_bv 8 0) bs ->
  (1 <= p <= 7)%Z -> ((src + p) mod 8 = 0)%Z -> (p <= Z.of_nat (length bs))%Z ->
  rdn SEGS (fun _ => None) (Z_to_bv 64 (src + p)) 8 = Some wd -> strlen_stop (Z_to_bv 64 (bytes_le_to_Z wd)) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (1 <= kR)%Z -> (RB10_small <= bR)%Z ->
  (forall A' m' vm' regs' (name : Z), W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C Ar s m m' ->
     getr regs' 10 = Z_to_bv 64 0 ->
     sela_at (alloc_top (c_vm C)) A' m' sela arr (k + 1) (upd sels k sel) (upd vs k (set_name v name)) (upd nms k bs) ->
     live A (Z_to_bv 64 name) = None -> live (c_A0 C) (Z_to_bv 64 name) = None ->
     (forall q, q <> Z_to_bv 64 name -> live A' q = live A q) ->
     aroom A' vm' (kR - 1) (bR - RB10_small) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x277b4 : word) m al_rom) md) S.
Proof.
  intros C Ar A m md regs s sela arr k sel src p sels vs nms v bs wd ret S CK HW SUBr H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 H13
         SLA Hk SA Hvn LsaR LarR LseR Lsa0 Lar0 Lse0 NB Hsrc0 Hsrc1 Hlen Rlit NZ Hp Hal Hpl Rwd STOP kR bR HRM HRK HRB HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  assert (HsS : (c_top C - LSTK + 96 <= s)%Z) by (unfold CALLOC_STACK, ALLOC_STACK in Hlo; lia).
  pose proof SLA as (_ & (Gsa & TOPsa & ALsa) & Lsa & Rsa & (Gar & TOPar & ALar) & Lar & NEar & _).
  pose proof SA as (_ & _ & (Gse & TOPse & ALse) & Lse & Rse & _).
  pose proof (REC_rd' SEGS m sel _ 5 8 (Z_to_bv 64 (sel + 24)) (v_name v) Rse ltac:(cbn; lia) eq_refl eq_refl eq_refl) as Rname. rewrite Hvn in Rname.
  destruct (as_A al_rom regs m s sela sel src ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (bok_mod8 _ _ _ (conj Gse (conj TOPse ALse)))
              (W_sok_win C A m md (s - 64) 64 CK HW ltac:(lia) ltac:(cbn; lia)) Rname H2 H1 H10 H11 H12 H13)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q8 & Q9 & Q18 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := AAF m s sel ret regs).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold AAF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (aacells_AAF m s sel ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1. rewrite <- H1 in CE1.
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x45480) by (rewrite (AG1 4) by notin_lit; exact H4).
  apply (stringNew_W C A M1 md r1 (s - 64) src p bs wd (Z_to_bv 64 0x27914) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 Hsrc0 Hsrc1 Hlen Rlit NZ Hp Hal Hpl Rwd STOP kR bR HRM HRK HRB).
  intros A2 m2 vm2 r2 name HW2 CS2 PM2 R10 NA2 LnA Ln0 LEQ HRM2.
  replace (Z_to_bv 64 0x27914) with (0x27914 : word) by (apply bv_eq; reflexivity).
  pose proof NA2 as ((Gnm & TOPnm & _) & Lnm & _).
  assert (SUB2 : sub_live A A2) by (eapply sub_live_new; eassumption).
  assert (PMa : POSTM C A s m m2) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PM2]; lia]).
  pose proof (sela_at_keep _ A A2 m m2 _ _ _ _ _ _ AT SLA SUB2 (proj2 PMa)) as SLA2.
  pose proof (sel_at_keep _ A A2 m m2 _ _ AT SA SUB2 (proj2 PMa)) as SA2.
  pose proof SLA2 as (_ & _ & Lsa2 & Rsa2 & _ & Lar2 & _). pose proof SA2 as (_ & _ & _ & Lse2 & _).
  pose proof (live_apart C A2 m2 _ _ _ _ _ CK HW2 Lsa2 Lse2 ltac:(apply zbv_ne; [lia | lia |]; exact (not_eq_sym (proj1 (NB sel (or_introl eq_refl))))) ltac:(lia) ltac:(lia)) as D1.
  pose proof (live_apart C A2 m2 _ _ _ _ _ CK HW2 Lsa2 Lar2 ltac:(apply zbv_ne; [lia | lia |]; exact (not_eq_sym NEar)) ltac:(lia) ltac:(lia)) as D2.
  pose proof (live_apart C A2 m2 _ _ _ _ _ CK HW2 Lse2 Lar2 ltac:(apply zbv_ne; [lia | lia |]; exact (proj1 (proj2 (NB sel (or_introl eq_refl))))) ltac:(lia) ltac:(lia)) as D3.
  rewrite !u_Z2bv in D1, D2, D3 by lia.
  pose proof (REC_rd' SEGS m2 sela _ 0 4 (Z_to_bv 64 sela) k Rsa2 ltac:(cbn; lia) eq_refl ltac:(cbn [fld_off sela_flds Z.of_nat]; f_equal; lia) eq_refl) as Rn.
  pose proof (REC_rd' SEGS m2 sela _ 1 4 (Z_to_bv 64 (sela + 4)) 50 Rsa2 ltac:(cbn; lia) eq_refl eq_refl eq_refl) as Rna.
  pose proof (REC_rd' SEGS m2 sela _ 2 8 (Z_to_bv 64 (sela + 8)) arr Rsa2 ltac:(cbn; lia) eq_refl eq_refl eq_refl) as Rarr.
  pose proof (aacells_FRM C M1 m2 s _ _ _ _ _ _ CK (proj1 PM2) ltac:(lia) ltac:(lia) CE1) as CE2.
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 64)) by (rewrite (CS2 2%bv cs2); exact Q2).
  assert (E8 : getr r2 8 = Z_to_bv 64 sela) by (rewrite (CS2 8%bv cs8); exact Q8).
  assert (E9 : getr r2 9 = Z_to_bv 64 sel) by (rewrite (CS2 9%bv cs9); exact Q9).
  assert (E18 : getr r2 18 = Z_to_bv 64 0) by (rewrite (CS2 18%bv cs18); exact Q18).
  destruct (as_B al_rom r2 m2 s sela sel arr k name (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hk ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              (bok_mod8 _ _ _ (conj Gsa (conj TOPsa ALsa))) (bok_mod8 _ _ _ (conj Gar (conj TOPar ALar))) Rn Rna Rarr
              (W_sok_blk C A2 m2 _ _ _ (sel + 24) 8 CK HW2 Lse2 ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; cbn; lia) ltac:(rewrite u_Z2bv by lia; lia))
              (W_sok_blk C A2 m2 _ _ _ (arr + 8 * k) 8 CK HW2 Lar2 ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; cbn; lia) ltac:(rewrite u_Z2bv by lia; lia))
              (W_sok_blk C A2 m2 _ _ _ sela 4 CK HW2 Lsa2 ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; cbn; lia) ltac:(rewrite u_Z2bv by lia; lia))
              ltac:(rewrite H1; exact Hret) CE2 E2 R10 E8 E9 E18)
    as (r3 & RUN3 & P2 & P1 & P10 & P8 & P9 & P18 & P19 & P20 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  set (Ma := wbytes m2 (Z_to_bv 64 (sel + 24)) (word_to_le_bytes 8 (Z_to_bv 64 name))).
  set (Mb := wbytes Ma (Z_to_bv 64 (arr + 8 * k)) (word_to_le_bytes 8 (Z_to_bv 64 sel))).
  set (M3 := wbytes Mb (Z_to_bv 64 sela) (word_to_le_bytes 4 (Z_to_bv 64 (k + 1)))).
  assert (SUBr2 : sub_live Ar A2) by (eapply sub_live_trans; eassumption).
  assert (PMr : POSTM C Ar s m m2) by (apply (POSTM_sub C Ar A _ _ _ SUBr); exact PMa).
  assert (WPa : W C A2 Ma (with_vmmaps vm2 md) /\ POSTM C Ar s m Ma)
    by (subst Ma; apply (WP_blk C Ar A2 m m2 _ (Z_to_bv 64 sel) _ 32 _ s CK (conj HW2 PMr) Lse2 LseR Lse0 SUBr2); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia).
  assert (WPb : W C A2 Mb (with_vmmaps vm2 md) /\ POSTM C Ar s m Mb)
    by (subst Mb; apply (WP_blk C Ar A2 m Ma _ (Z_to_bv 64 arr) _ 400 _ s CK WPa Lar2 LarR Lar0 SUBr2); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia).
  assert (WP3 : W C A2 M3 (with_vmmaps vm2 md) /\ POSTM C Ar s m M3)
    by (subst M3; apply (WP_blk C Ar A2 m Mb _ (Z_to_bv 64 sela) _ 16 _ s CK WPb Lsa2 LsaR Lsa0 SUBr2); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia).
  (* [comment removed for export] *)
  assert (FRESH : forall q n, live A (Z_to_bv 64 q) = Some n -> (0 <= q < 2 ^ 64)%Z -> q <> name).
  { intros q n Lq Hq E. subst q. rewrite LnA in Lq. discriminate. }
  assert (NB' : forall q, sel_blk sel v q -> q <> sela /\ q <> arr /\ q <> name /\ forall i p', (0 <= i < k)%Z -> seln_blk (sels i) (vs i) p' -> p' <> q).
  { intros q Hq. destruct (NB q Hq) as (X1 & X2 & X3). split; [exact X1|]. split; [exact X2|]. split; [|exact X3].
    destruct (sel_blk_live _ A m sel v q SA Hq) as (n & Lq & Hn & G1 & G2). exact (FRESH q n Lq ltac:(lia)). }
  assert (NNo : forall i p', (0 <= i < k)%Z -> seln_blk (sels i) (vs i) p' -> p' <> name).
  { intros i p' Hi Hp'. destruct (sela_blk_live _ A m sela arr k sels vs nms i p' SLA Hi Hp') as (n & Lq & Hn & G1 & G2). exact (FRESH p' n Lq ltac:(lia)). }
  pose proof (sela_at_add C A2 m2 _ (alloc_top (c_vm C)) sela arr k sels vs nms sel v name bs Ma Mb M3 CK HW2 AT SLA2 Hk SA2 NA2 NB'
                (not_eq_sym (FRESH sela 16%Z Lsa ltac:(lia))) (not_eq_sym (FRESH arr 400%Z Lar ltac:(lia))) NNo eq_refl eq_refl eq_refl (proj1 WPa) (proj1 WPb)) as SLA3.
  rewrite H1. apply (HK A2 M3 vm2 r3 name (proj1 WP3)).
  - assert (REST : forall x, In x aa_rest -> getr r3 x = getr regs x).
    { intros x Hx. unfold aa_rest in Hx. cbn [In] in Hx.
      repeat (destruct Hx as [<-|Hx];
              [rewrite (AG3 _) by notin_lit;
               first [ rewrite (CS2 _ cs3) | rewrite (CS2 _ cs4) | rewrite (CS2 _ cs21) | rewrite (CS2 _ cs22) | rewrite (CS2 _ cs23)
                     | rewrite (CS2 _ cs24) | rewrite (CS2 _ cs25) | rewrite (CS2 _ cs26) | rewrite (CS2 _ cs27) ];
               rewrite (AG1 _) by notin_lit; reflexivity|]). destruct Hx. }
    apply cs_kept_intro; first [ rewrite P2; symmetry; exact H2 | exact P8 | exact P9 | exact P18 | exact P19 | exact P20 | apply REST; unfold aa_rest; in_lit ].
  - exact (proj2 WP3).
  - exact P10.
  - exact SLA3.
  - exact LnA.
  - exact Ln0.
  - exact LEQ.
  - exact HRM2.
Qed.

End SelBrick.
