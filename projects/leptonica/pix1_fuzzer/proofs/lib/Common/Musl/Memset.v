(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Import StartupTac RefMemcpyLib ShapeAlg PureModel.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Reloc Require Import RelocKit RCode_1c000_1d000.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := rl_segs.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition memset_clob : list reg := [11; 12; 13; 14; 15; 16]%list.

Section MS.
  Context {fx : FPState} {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL}.
  Variable M : word -> option byte.
  Variables d n : Z.
  Variable rom : word -> option byte.
  Variable ret : word.
  Hypothesis Hd : (0 <= d)%Z.
  Hypothesis Hn : (1 <= n)%Z.
  Hypothesis Hn64 : (n < 2 ^ 64)%Z.
  Hypothesis Hdn : (d + n <= 2 ^ 64)%Z.
  Hypothesis Hok : store_ok SEGS M (Z_to_bv 64 d) (Z.to_nat n) = true.
  Hypothesis Hret : ret_ok ret.

  #[local] Notation ZF l := (zf M d l) (only parsing).

  (* [comment removed for export] *)
  Lemma ok_at : forall l o (w : nat), (0 <= o)%Z -> (o + Z.of_nat w <= n)%Z ->
    store_ok SEGS (ZF l) (Z_to_bv 64 (d + o)) w = true.
  Proof.
    intros l o w Ho Hw. apply store_ok_zf.
    destruct w as [|w']; [reflexivity|].
    eapply (store_ok_sub SEGS M (Z_to_bv 64 d) (Z_to_bv 64 (d + o)) (Z.to_nat n) (S w'));
      [ | exact Hok | | ]; rewrite ?u_Z2bv by lia; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma zst_sb : forall regs pc w rs1 rs2 (imm : bv 12) l e o,
    fetch_word SEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = Z_to_bv 64 e -> (e + bv_signed imm = d + o)%Z ->
    getr regs rs2 = Z_to_bv 64 0 ->
    (0 <= o)%Z -> (o + 1 <= n)%Z ->
    RiscvSemantics.step SEGS (mkst regs pc (ZF l) rom) =
    MachineOk (mkst regs (v_addi pc 4) (ZF ((o, o + 1)%Z :: l)) rom).
  Proof.
    intros regs pc w rs1 rs2 imm l e o Hf He HD Hrs1 Heo Hrs2 Ho Hon.
    rewrite (MmapSim.step_sb_at SEGS regs pc (ZF l) rom w rs1 rs2 imm (Z_to_bv 64 (d + o)) (Z_to_bv 64 0) (Z_to_bv 8 0) Hf He HD).
    - f_equal. f_equal. change [Z_to_bv 8 0] with (zeros 1). rewrite wbytes_zf by lia. reflexivity.
    - rewrite Hrs1, zbv_addi. f_equal. exact Heo.
    - exact Hrs2.
    - reflexivity.
    - apply (ok_at l o 1); lia.
  Qed.

  Lemma zst_sw : forall regs pc w rs1 rs2 (imm : bv 12) l e o,
    fetch_word SEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ4 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = Z_to_bv 64 e -> (e + bv_signed imm = d + o)%Z ->
    getr regs rs2 = Z_to_bv 64 0 ->
    (0 <= o)%Z -> (o + 4 <= n)%Z ->
    RiscvSemantics.step SEGS (mkst regs pc (ZF l) rom) =
    MachineOk (mkst regs (v_addi pc 4) (ZF ((o, o + 4)%Z :: l)) rom).
  Proof.
    intros regs pc w rs1 rs2 imm l e o Hf He HD Hrs1 Heo Hrs2 Ho Hon.
    rewrite (step_sw_at SEGS regs pc (ZF l) rom w rs1 rs2 imm (Z_to_bv 64 (d + o)) (Z_to_bv 64 0) Hf He HD).
    - f_equal. f_equal. rewrite word_to_le_bytes_zero. rewrite wbytes_zf by lia. reflexivity.
    - rewrite Hrs1, zbv_addi. f_equal. exact Heo.
    - exact Hrs2.
    - apply (ok_at l o 4); lia.
  Qed.

  Lemma zst_sd : forall regs pc w rs1 rs2 (imm : bv 12) l e o,
    fetch_word SEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ8 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = Z_to_bv 64 e -> (e + bv_signed imm = d + o)%Z ->
    getr regs rs2 = Z_to_bv 64 0 ->
    (0 <= o)%Z -> (o + 8 <= n)%Z ->
    RiscvSemantics.step SEGS (mkst regs pc (ZF l) rom) =
    MachineOk (mkst regs (v_addi pc 4) (ZF ((o, o + 8)%Z :: l)) rom).
  Proof.
    intros regs pc w rs1 rs2 imm l e o Hf He HD Hrs1 Heo Hrs2 Ho Hon.
    rewrite (step_sd_at SEGS regs pc (ZF l) rom w rs1 rs2 imm (Z_to_bv 64 (d + o)) (Z_to_bv 64 0) Hf He HD).
    - f_equal. f_equal. rewrite word_to_le_bytes_zero. rewrite wbytes_zf by lia. reflexivity.
    - rewrite Hrs1, zbv_addi. f_equal. exact Heo.
    - exact Hrs2.
    - apply (ok_at l o 8); lia.
  Qed.

  (* [comment removed for export] *)
  Ltac zst F D oo :=
    chain_step;
    [ reflexivity
    | lazymatch type of D with
      | decode_any _ = Some (Store SZ1 _ _ _, _) => eapply zst_sb with (o := oo)
      | decode_any _ = Some (Store SZ4 _ _ _, _) => eapply zst_sw with (o := oo)
      | decode_any _ = Some (Store SZ8 _ _ _, _) => eapply zst_sd with (o := oo)
      end;
      [ exact F | reflexivity | exact D
      | gres; pin; reflexivity
      | imm_norm; lia
      | gres; pin; reflexivity
      | lia | lia ]
    | step_simpl ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma p1_run : forall regs,
    getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (rl dF_1cdb8 0x1cdb8) (ZF []) rom)
                  (mkst regs' (rl dF_1cdb8 0x1cdcc) (ZF [(n - 1, n - 1 + 1); (0, 0 + 1)]%Z) rom)
      /\ getr regs' 10 = Z_to_bv 64 d /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 n
      /\ getr regs' 13 = Z_to_bv 64 (d + n) /\ getr regs' 14 = Z_to_bv 64 3
      /\ regs_agree (fun r => In r memset_clob) regs regs'.
  Proof.
    intros regs H10 H11 H12.
    eexists. split.
    - stepb_ft F_1cdb8 D_1cdb8 ltac:(condZ).                 (* [comment removed for export] *)
      zst F_1cdbc D_1cdbc 0%Z.                                (* [comment removed for export] *)
      zv F_1cdc0 D_1cdc0 (Z_to_bv 64 (d + n)).               (* [comment removed for export] *)
      sn F_1cdc4 D_1cdc4.                                     (* [comment removed for export] *)
      zst F_1cdc8 D_1cdc8 (n - 1)%Z.                          (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.


  #[local] Notation C := (fun r : reg => In r memset_clob) (only parsing).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma p1_ret : forall regs l,
    getr regs 1 = ret -> getr regs 12 = Z_to_bv 64 n -> getr regs 14 = Z_to_bv 64 3 -> (n <= 2)%Z ->
    msteps SEGS (mkst regs (rl dF_1cdb8 0x1cdcc) (ZF l) rom) (mkst regs ret (ZF l) rom).
  Proof.
    intros regs l H1 H12 H14 Hle.
    stepb_tk F_1cdcc D_1cdcc ltac:(condZ).                   (* [comment removed for export] *)
    stepret F_1ceac D_1ceac ret ltac:(pin; reflexivity).
    apply mst_refl.
  Qed.

  Lemma p1_cont : forall regs l,
    getr regs 12 = Z_to_bv 64 n -> getr regs 14 = Z_to_bv 64 3 -> (3 <= n)%Z ->
    msteps SEGS (mkst regs (rl dF_1cdb8 0x1cdcc) (ZF l) rom) (mkst regs (rl dF_1cdb8 0x1cdd0) (ZF l) rom).
  Proof.
    intros regs l H12 H14 Hle.
    stepb_ft F_1cdcc D_1cdcc ltac:(condZ).
    apply mst_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma p2_run : forall regs l,
    getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 (d + n) ->
    (3 <= n)%Z ->
    exists regs',
      msteps SEGS (mkst regs (rl dF_1cdb8 0x1cdd0) (ZF l) rom)
                  (mkst regs' (rl dF_1cdb8 0x1cde4)
                        (ZF ((n - 2, n - 2 + 1) :: (n - 3, n - 3 + 1) :: (2, 2 + 1) :: (1, 1 + 1) :: l)%Z) rom)
      /\ getr regs' 14 = Z_to_bv 64 7
      /\ regs_agree (fun r : reg => In r [14]%list) regs regs'.
  Proof.
    intros regs l H10 H11 H13 Hn3.
    eexists. split.
    - zst F_1cdd0 D_1cdd0 1%Z.                                (* [comment removed for export] *)
      zst F_1cdd4 D_1cdd4 2%Z.                                (* [comment removed for export] *)
      sn F_1cdd8 D_1cdd8.                                     (* [comment removed for export] *)
      zst F_1cddc D_1cddc (n - 3)%Z.                          (* [comment removed for export] *)
      zst F_1cde0 D_1cde0 (n - 2)%Z.                          (* [comment removed for export] *)
      apply mst_refl.
    - split; [gres; reflexivity | solve_regs_agree].
  Qed.

  Lemma p2_ret : forall regs l,
    getr regs 1 = ret -> getr regs 12 = Z_to_bv 64 n -> getr regs 14 = Z_to_bv 64 7 -> (n <= 6)%Z ->
    msteps SEGS (mkst regs (rl dF_1cdb8 0x1cde4) (ZF l) rom) (mkst regs ret (ZF l) rom).
  Proof.
    intros regs l H1 H12 H14 Hle.
    stepb_tk F_1cde4 D_1cde4 ltac:(condZ).
    stepret F_1ceac D_1ceac ret ltac:(pin; reflexivity).
    apply mst_refl.
  Qed.

  Lemma p2_cont : forall regs l,
    getr regs 12 = Z_to_bv 64 n -> getr regs 14 = Z_to_bv 64 7 -> (7 <= n)%Z ->
    msteps SEGS (mkst regs (rl dF_1cdb8 0x1cde4) (ZF l) rom) (mkst regs (rl dF_1cdb8 0x1cde8) (ZF l) rom).
  Proof.
    intros regs l H12 H14 Hle.
    stepb_ft F_1cde4 D_1cde4 ltac:(condZ).
    apply mst_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma p3_run : forall regs l,
    getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 (d + n) ->
    (7 <= n)%Z ->
    exists regs',
      msteps SEGS (mkst regs (rl dF_1cdb8 0x1cde8) (ZF l) rom)
                  (mkst regs' (rl dF_1cdb8 0x1cdf4) (ZF ((n - 4, n - 4 + 1) :: (3, 3 + 1) :: l)%Z) rom)
      /\ getr regs' 15 = Z_to_bv 64 9
      /\ regs_agree (fun r : reg => In r [15]%list) regs regs'.
  Proof.
    intros regs l H10 H11 H13 Hn7.
    eexists. split.
    - zst F_1cde8 D_1cde8 3%Z.                                (* [comment removed for export] *)
      sn F_1cdec D_1cdec.                                     (* [comment removed for export] *)
      zst F_1cdf0 D_1cdf0 (n - 4)%Z.                          (* [comment removed for export] *)
      apply mst_refl.
    - split; [gres; reflexivity | solve_regs_agree].
  Qed.

  Lemma p3_ret : forall regs l,
    getr regs 1 = ret -> getr regs 12 = Z_to_bv 64 n -> getr regs 15 = Z_to_bv 64 9 -> (n <= 8)%Z ->
    msteps SEGS (mkst regs (rl dF_1cdb8 0x1cdf4) (ZF l) rom) (mkst regs ret (ZF l) rom).
  Proof.
    intros regs l H1 H12 H15 Hle.
    stepb_tk F_1cdf4 D_1cdf4 ltac:(condZ).
    stepret F_1ceac D_1ceac ret ltac:(pin; reflexivity).
    apply mst_refl.
  Qed.

  Lemma p3_cont : forall regs l,
    getr regs 12 = Z_to_bv 64 n -> getr regs 15 = Z_to_bv 64 9 -> (9 <= n)%Z ->
    msteps SEGS (mkst regs (rl dF_1cdb8 0x1cdf4) (ZF l) rom) (mkst regs (rl dF_1cdb8 0x1cdf8) (ZF l) rom).
  Proof.
    intros regs l H12 H15 Hle.
    stepb_ft F_1cdf4 D_1cdf4 ltac:(condZ).
    apply mst_refl.
  Qed.


  (* [comment removed for export] *)
  Lemma p4_run : forall regs l k t m,
    getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 n ->
    ((- d) mod 4 = k)%Z -> ((n - k) mod 4 = t)%Z -> (m = n - k - t)%Z ->
    (0 <= k <= 3)%Z -> (0 <= t <= 3)%Z -> (9 <= n)%Z ->
    exists regs',
      msteps SEGS (mkst regs (rl dF_1cdb8 0x1cdf8) (ZF l) rom)
                  (mkst regs' (rl dF_1cdb8 0x1ce2c) (ZF ((k + m - 4, k + m - 4 + 4) :: (k, k + 4) :: l)%Z) rom)
      /\ getr regs' 10 = Z_to_bv 64 d /\ getr regs' 11 = Z_to_bv 64 (d + k) /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 13 = Z_to_bv 64 (d + k + m) /\ getr regs' 14 = Z_to_bv 64 m
      /\ getr regs' 15 = getr regs 15 /\ getr regs' 16 = Z_to_bv 64 0
      /\ regs_agree C regs regs'.
  Proof.
    intros regs l k t m H10 H11 H12 Hk Ht Hm Hk3 Ht3 Hn9.
    eexists. split.
    - sn F_1cdf8 D_1cdf8.                                     (* [comment removed for export] *)
      stepiv F_1cdfc D_1cdfc (Z_to_bv 64 0) ltac:(gres; pin; reflexivity).   (* [comment removed for export] *)
      sn F_1ce00 D_1ce00.                                     (* [comment removed for export] *)
      stepiv F_1ce04 D_1ce04 (Z_to_bv 64 k)
        ltac:(gres; pin; rewrite negw_and3, (u_Z2bv d) by lia; f_equal; exact Hk).   (* [comment removed for export] *)
      sn F_1ce08 D_1ce08.                                     (* [comment removed for export] *)
      zv F_1ce0c D_1ce0c (Z_to_bv 64 (n - k)).               (* [comment removed for export] *)
      zv F_1ce10 D_1ce10 (Z_to_bv 64 (d + k)).               (* [comment removed for export] *)
      sn F_1ce14 D_1ce14.                                     (* [comment removed for export] *)
      stepiv F_1ce18 D_1ce18 (Z_to_bv 64 m)
        ltac:(gres; pin; imm_norm; rewrite andi_m4, !(u_Z2bv (n - k)) by lia; f_equal; lia).   (* [comment removed for export] *)
      sn F_1ce1c D_1ce1c.                                     (* [comment removed for export] *)
      zst F_1ce20 D_1ce20 k.                                  (* [comment removed for export] *)
      zv F_1ce24 D_1ce24 (Z_to_bv 64 (d + k + m)).           (* [comment removed for export] *)
      zst F_1ce28 D_1ce28 (k + m - 4)%Z.                      (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma p4_ret : forall regs l m,
    getr regs 1 = ret -> getr regs 14 = Z_to_bv 64 m -> getr regs 15 = Z_to_bv 64 9 ->
    (0 <= m <= 8)%Z ->
    msteps SEGS (mkst regs (rl dF_1cdb8 0x1ce2c) (ZF l) rom) (mkst regs ret (ZF l) rom).
  Proof.
    intros regs l m H1 H14 H15 Hle.
    stepb_tk F_1ce2c D_1ce2c ltac:(condZ).
    stepret F_1ceac D_1ceac ret ltac:(pin; reflexivity).
    apply mst_refl.
  Qed.

  Lemma p4_cont : forall regs l m,
    getr regs 14 = Z_to_bv 64 m -> getr regs 15 = Z_to_bv 64 9 -> (9 <= m <= n)%Z ->
    msteps SEGS (mkst regs (rl dF_1cdb8 0x1ce2c) (ZF l) rom) (mkst regs (rl dF_1cdb8 0x1ce30) (ZF l) rom).
  Proof.
    intros regs l m H14 H15 Hle.
    stepb_ft F_1ce2c D_1ce2c ltac:(condZ).
    apply mst_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma p5_run : forall regs l k m,
    getr regs 11 = Z_to_bv 64 (d + k) -> getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 (d + k + m) ->
    (0 <= k)%Z -> (12 <= m)%Z -> (k + m <= n)%Z ->
    exists regs',
      msteps SEGS (mkst regs (rl dF_1cdb8 0x1ce30) (ZF l) rom)
                  (mkst regs' (rl dF_1cdb8 0x1ce44)
                     (ZF ((k + m - 8, k + m - 8 + 4) :: (k + m - 12, k + m - 12 + 4)
                          :: (k + 8, k + 8 + 4) :: (k + 4, k + 4 + 4) :: l)%Z) rom)
      /\ getr regs' 15 = Z_to_bv 64 25
      /\ regs_agree (fun r : reg => In r [15]%list) regs regs'.
  Proof.
    intros regs l k m H11 H12 H13 Hk Hm Hkm.
    eexists. split.
    - zst F_1ce30 D_1ce30 (k + 4)%Z.                          (* [comment removed for export] *)
      zst F_1ce34 D_1ce34 (k + 8)%Z.                          (* [comment removed for export] *)
      sn F_1ce38 D_1ce38.                                     (* [comment removed for export] *)
      zst F_1ce3c D_1ce3c (k + m - 12)%Z.                     (* [comment removed for export] *)
      zst F_1ce40 D_1ce40 (k + m - 8)%Z.                      (* [comment removed for export] *)
      apply mst_refl.
    - split; [gres; reflexivity | solve_regs_agree].
  Qed.

  Lemma p5_ret : forall regs l m,
    getr regs 1 = ret -> getr regs 14 = Z_to_bv 64 m -> getr regs 15 = Z_to_bv 64 25 ->
    (0 <= m <= 24)%Z ->
    msteps SEGS (mkst regs (rl dF_1cdb8 0x1ce44) (ZF l) rom) (mkst regs ret (ZF l) rom).
  Proof.
    intros regs l m H1 H14 H15 Hle.
    stepb_tk F_1ce44 D_1ce44 ltac:(condZ).
    stepret F_1ceac D_1ceac ret ltac:(pin; reflexivity).
    apply mst_refl.
  Qed.

  Lemma p5_cont : forall regs l m,
    getr regs 14 = Z_to_bv 64 m -> getr regs 15 = Z_to_bv 64 25 -> (25 <= m <= n)%Z ->
    msteps SEGS (mkst regs (rl dF_1cdb8 0x1ce44) (ZF l) rom) (mkst regs (rl dF_1cdb8 0x1ce48) (ZF l) rom).
  Proof.
    intros regs l m H14 H15 Hle.
    stepb_ft F_1ce44 D_1ce44 ltac:(condZ).
    apply mst_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma p6_run : forall regs l k m e,
    getr regs 11 = Z_to_bv 64 (d + k) -> getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 (d + k + m) ->
    getr regs 14 = Z_to_bv 64 m ->
    ((d + k) mod 4 = 0)%Z -> ((d + k) mod 8 = e)%Z -> (0 <= e <= 4)%Z ->
    (0 <= k)%Z -> (28 <= m)%Z -> (k + m <= n)%Z ->
    exists regs',
      msteps SEGS (mkst regs (rl dF_1cdb8 0x1ce48) (ZF l) rom)
                  (mkst regs' (rl dF_1cdb8 0x1ce78)
                     (ZF ((k + m - 16, k + m - 16 + 4) :: (k + m - 20, k + m - 20 + 4)
                          :: (k + m - 24, k + m - 24 + 4) :: (k + m - 28, k + m - 28 + 4)
                          :: (k + 24, k + 24 + 4) :: (k + 20, k + 20 + 4)
                          :: (k + 16, k + 16 + 4) :: (k + 12, k + 12 + 4) :: l)%Z) rom)
      /\ getr regs' 11 = Z_to_bv 64 (d + k) /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 14 = Z_to_bv 64 (m - 24 - e) /\ getr regs' 15 = Z_to_bv 64 (24 + e)
      /\ getr regs' 16 = Z_to_bv 64 32
      /\ regs_agree (fun r : reg => In r [14; 15; 16]%list) regs regs'.
  Proof.
    intros regs l k m e H11 H12 H13 H14 Hal4 He He4 Hk Hm Hkm.
    eexists. split.
    - zst F_1ce48 D_1ce48 (k + 12)%Z.                         (* [comment removed for export] *)
      zst F_1ce4c D_1ce4c (k + 16)%Z.                         (* [comment removed for export] *)
      zst F_1ce50 D_1ce50 (k + 20)%Z.                         (* [comment removed for export] *)
      zst F_1ce54 D_1ce54 (k + 24)%Z.                         (* [comment removed for export] *)
      stepiv F_1ce58 D_1ce58 (Z_to_bv 64 e)
        ltac:(gres; pin; imm_norm; rewrite andi_4_al4 by (rewrite (u_Z2bv (d + k)) by lia; exact Hal4);
              rewrite (u_Z2bv (d + k)) by lia; f_equal; exact He).      (* [comment removed for export] *)
      sn F_1ce5c D_1ce5c.                                     (* [comment removed for export] *)
      zv F_1ce60 D_1ce60 (Z_to_bv 64 (24 + e)).              (* [comment removed for export] *)
      zv F_1ce64 D_1ce64 (Z_to_bv 64 (m - 24 - e)).          (* [comment removed for export] *)
      zst F_1ce68 D_1ce68 (k + m - 28)%Z.                     (* [comment removed for export] *)
      zst F_1ce6c D_1ce6c (k + m - 24)%Z.                     (* [comment removed for export] *)
      zst F_1ce70 D_1ce70 (k + m - 20)%Z.                     (* [comment removed for export] *)
      zst F_1ce74 D_1ce74 (k + m - 16)%Z.                     (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma p6_ret : forall regs l m2,
    getr regs 1 = ret -> getr regs 14 = Z_to_bv 64 m2 -> getr regs 16 = Z_to_bv 64 32 ->
    (0 <= m2 < 32)%Z ->
    msteps SEGS (mkst regs (rl dF_1cdb8 0x1ce78) (ZF l) rom) (mkst regs ret (ZF l) rom).
  Proof.
    intros regs l m2 H1 H14 H16 Hle.
    stepb_tk F_1ce78 D_1ce78 ltac:(condZ).
    stepret F_1ceac D_1ceac ret ltac:(pin; reflexivity).
    apply mst_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma p7_run : forall regs l k e m2,
    getr regs 11 = Z_to_bv 64 (d + k) -> getr regs 12 = Z_to_bv 64 0 ->
    getr regs 14 = Z_to_bv 64 m2 -> getr regs 15 = Z_to_bv 64 (24 + e) -> getr regs 16 = Z_to_bv 64 32 ->
    (32 <= m2 <= n)%Z ->
    exists regs',
      msteps SEGS (mkst regs (rl dF_1cdb8 0x1ce78) (ZF l) rom) (mkst regs' (rl dF_1cdb8 0x1ce90) (ZF l) rom)
      /\ getr regs' 11 = Z_to_bv 64 (d + (k + 24 + e)) /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 13 = Z_to_bv 64 31 /\ getr regs' 14 = Z_to_bv 64 m2
      /\ regs_agree (fun r : reg => In r [11; 12; 13]%list) regs regs'.
  Proof.
    intros regs l k e m2 H11 H12 H14 H15 H16 Hm2.
    eexists. split.
    - stepb_ft F_1ce78 D_1ce78 ltac:(condZ).                 (* [comment removed for export] *)
      stepiv F_1ce7c D_1ce7c (Z_to_bv 64 0) ltac:(gres; pin; reflexivity).   (* [comment removed for export] *)
      zv F_1ce80 D_1ce80 (Z_to_bv 64 (d + (k + 24 + e))).   (* [comment removed for export] *)
      stepiv F_1ce84 D_1ce84 (Z_to_bv 64 0) ltac:(gres; pin; reflexivity).   (* [comment removed for export] *)
      sn F_1ce88 D_1ce88.                                     (* [comment removed for export] *)
      sn F_1ce8c D_1ce8c.                                     (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma zf_merge32 : forall o0 o l, (o0 <= o)%Z ->
    ZF ((o + 24, o + 24 + 8) :: (o + 16, o + 16 + 8) :: (o + 8, o + 8 + 8) :: (o, o + 8) :: (o0, o) :: l)%Z
    = ZF ((o0, o + 32)%Z :: l).
  Proof. intros o0 o l Ho. apply zf_ext. intros i. inzr_tac. Qed.

  (* [comment removed for export] *)
  Lemma loop_run : forall q regs l o0 o r,
    getr regs 1 = ret -> getr regs 11 = Z_to_bv 64 (d + o) -> getr regs 12 = Z_to_bv 64 0 ->
    getr regs 13 = Z_to_bv 64 31 -> getr regs 14 = Z_to_bv 64 r ->
    (0 <= o0 <= o)%Z -> (o + r <= n)%Z ->
    (32 * (Z.of_nat q + 1) <= r < 32 * (Z.of_nat q + 1) + 32)%Z ->
    exists regs',
      msteps SEGS (mkst regs (rl dF_1cdb8 0x1ce90) (ZF ((o0, o) :: l)) rom)
                  (mkst regs' ret (ZF ((o0, o + 32 * (Z.of_nat q + 1))%Z :: l)) rom)
      /\ regs_agree (fun r : reg => In r [11; 14]%list) regs regs'.
  Proof.
    induction q as [|q IH]; intros regs l o0 o r H1 H11 H12 H13 H14 Ho Hor Hq.
    - eexists. split.
      + zst F_1ce90 D_1ce90 o.                                (* [comment removed for export] *)
        zst F_1ce94 D_1ce94 (o + 8)%Z.                        (* [comment removed for export] *)
        zst F_1ce98 D_1ce98 (o + 16)%Z.                       (* [comment removed for export] *)
        zst F_1ce9c D_1ce9c (o + 24)%Z.                       (* [comment removed for export] *)
        zv F_1cea0 D_1cea0 (Z_to_bv 64 (r - 32)).             (* [comment removed for export] *)
        zv F_1cea4 D_1cea4 (Z_to_bv 64 (d + (o + 32))).       (* [comment removed for export] *)
        stepb_ft F_1cea8 D_1cea8 ltac:(condZ).               (* [comment removed for export] *)
        stepret F_1ceac D_1ceac ret ltac:(pin; reflexivity).
        rewrite zf_merge32 by lia.
        replace (o + 32 * (Z.of_nat 0 + 1))%Z with (o + 32)%Z by lia.
        apply mst_refl.
      + solve_regs_agree.
    - eapply (runs_trans SEGS _ (fun rg => mkst rg (rl dF_1cdb8 0x1ce90) (ZF ((o0, o + 32)%Z :: l)) rom)
               (fun rg => getr rg 1 = ret /\ getr rg 11 = Z_to_bv 64 (d + (o + 32)) /\ getr rg 12 = Z_to_bv 64 0
                          /\ getr rg 13 = Z_to_bv 64 31 /\ getr rg 14 = Z_to_bv 64 (r - 32)
                          /\ regs_agree (fun r : reg => In r [11; 14]%list) regs rg)).
      + eexists. split.
        * zst F_1ce90 D_1ce90 o.
          zst F_1ce94 D_1ce94 (o + 8)%Z.
          zst F_1ce98 D_1ce98 (o + 16)%Z.
          zst F_1ce9c D_1ce9c (o + 24)%Z.
          zv F_1cea0 D_1cea0 (Z_to_bv 64 (r - 32)).
          zv F_1cea4 D_1cea4 (Z_to_bv 64 (d + (o + 32))).
          stepb_tk F_1cea8 D_1cea8 ltac:(condZ).             (* [comment removed for export] *)
          rewrite zf_merge32 by lia.
          apply mst_refl.
        * cbv beta. repeat split; gres; pin; try reflexivity. solve_regs_agree.
      + cbv beta. intros r1 (R1 & R11 & R12 & R13 & R14 & AG).
        destruct (IH r1 l o0 (o + 32)%Z (r - 32)%Z R1 R11 R12 R13 R14 ltac:(lia) ltac:(lia) ltac:(lia))
          as (r2 & RUN & AG2).
        exists r2. split.
        * replace (o + 32 * (Z.of_nat (S q) + 1))%Z with (o + 32 + 32 * (Z.of_nat q + 1))%Z by lia. exact RUN.
        * eapply regs_agree_trans; eassumption.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma finish : forall regs regs' L,
    (forall i, inzrP i L <-> inzrP i [(0, n)]%Z) ->
    msteps SEGS (mkst regs (rl dF_1cdb8 0x1cdb8) (ZF []) rom) (mkst regs' ret (ZF L) rom) ->
    msteps SEGS (mkst regs (rl dF_1cdb8 0x1cdb8) M rom) (mkst regs' ret (ZF [(0, n)]%Z) rom).
  Proof.
    intros regs regs' L HL HR. rewrite <- (zf_extP M d L [(0, n)]%Z HL).
    rewrite zf_nil in HR. exact HR.
  Qed.

  Ltac agreeC H := first [ exact H | regs_agree_weaken H ].
  Ltac chainC :=
    lazymatch goal with
    | |- regs_agree _ ?a ?a => apply regs_agree_refl
    | H : regs_agree _ ?m ?c |- regs_agree _ ?a ?c =>
        first [ agreeC H | eapply (regs_agree_trans _ a m c); [ clear H; chainC | agreeC H ] ]
    end.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  Lemma k_facts : forall k, ((- d) mod 4 = k)%Z -> (0 <= k <= 3 /\ (d + k) mod 4 = 0)%Z.
  Proof.
    intros k Hk. pose proof (Z.mod_pos_bound (- d) 4 ltac:(lia)). split; [lia|].
    subst k. rewrite Zplus_mod_idemp_r. replace (d + - d)%Z with 0%Z by lia. reflexivity.
  Qed.

  Lemma e_facts : forall k e, ((d + k) mod 4 = 0)%Z -> ((d + k) mod 8 = e)%Z -> (e = 0 \/ e = 4)%Z.
  Proof.
    intros k e H4 He. pose proof (Z.mod_pos_bound (d + k) 8 ltac:(lia)).
    assert (E4 : (e mod 4 = 0)%Z).
    { subst e. change 8%Z with (2 ^ 3)%Z. rewrite mod4_mod_pow2' by lia. exact H4. }
    pose proof (Z.div_mod e 4 ltac:(lia)). lia.
  Qed.

  Lemma t_facts : forall k t, ((n - k) mod 4 = t)%Z -> (0 <= t <= 3 /\ n - k - t = 4 * ((n - k) / 4))%Z.
  Proof.
    intros k t Ht. pose proof (Z.mod_pos_bound (n - k) 4 ltac:(lia)). pose proof (Z.div_mod (n - k) 4 ltac:(lia)). lia.
  Qed.

  Lemma q_facts : forall m2, (32 <= m2)%Z ->
    (32 * (Z.of_nat (Z.to_nat (m2 / 32 - 1)) + 1) <= m2 < 32 * (Z.of_nat (Z.to_nat (m2 / 32 - 1)) + 1) + 32)%Z.
  Proof.
    intros m2 Hm2. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
    pose proof (Z.div_mod m2 32 ltac:(lia)). pose proof (Z.mod_pos_bound m2 32 ltac:(lia)). lia.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  (* [comment removed for export] *)
  Ltac lastl S := match type of S with msteps _ _ (mkst _ _ (zf _ _ ?l) _) => constr:(l) end.

  Theorem memset_run : forall regs,
    getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (rl dF_1cdb8 0x1cdb8) M rom) (mkst regs' ret (ZF [(0, n)]%Z) rom)
      /\ getr regs' 10 = Z_to_bv 64 d
      /\ regs_agree C regs regs'.
  Proof.
    intros regs H1 H10 H11 H12.
    destruct (p1_run regs H10 H11 H12) as (r1 & S1 & A10 & A11 & A12 & A13 & A14 & AG1).
    pose proof (AG1 1 ltac:(notin_list)) as A1. rewrite H1 in A1.
    destruct (Z.le_gt_cases n 2) as [Hn2|Hn2].
    { (* [comment removed for export] *)
      exists r1. split; [|split; [exact A10 | exact AG1]].
      eapply finish; [| eapply msteps_trans; [exact S1 | apply (p1_ret r1 _ A1 A12 A14 Hn2)]].
      intros i; cbn [inzrP]; lia. }
    let l := lastl S1 in destruct (p2_run r1 l A10 A11 A13 ltac:(lia)) as (r2 & S2 & B14 & AG2).
    pose proof (AG2 1 ltac:(notin_list)) as B1. rewrite A1 in B1.
    pose proof (AG2 10 ltac:(notin_list)) as B10. rewrite A10 in B10.
    pose proof (AG2 11 ltac:(notin_list)) as B11. rewrite A11 in B11.
    pose proof (AG2 12 ltac:(notin_list)) as B12. rewrite A12 in B12.
    pose proof (AG2 13 ltac:(notin_list)) as B13. rewrite A13 in B13.
    destruct (Z.le_gt_cases n 6) as [Hn6|Hn6].
    { (* [comment removed for export] *)
      exists r2. split; [|split; [exact B10 | chainC]].
      eapply finish; [| eapply msteps_trans; [exact S1 |
        eapply msteps_trans; [apply (p1_cont r1 _ A12 A14 ltac:(lia)) |
        eapply msteps_trans; [exact S2 | apply (p2_ret r2 _ B1 B12 B14 Hn6)]]]].
      intros i; cbn [inzrP]; lia. }
    let l := lastl S2 in destruct (p3_run r2 l B10 B11 B13 ltac:(lia)) as (r3 & S3 & C15 & AG3).
    pose proof (AG3 1 ltac:(notin_list)) as C1. rewrite B1 in C1.
    pose proof (AG3 10 ltac:(notin_list)) as C10. rewrite B10 in C10.
    pose proof (AG3 11 ltac:(notin_list)) as C11. rewrite B11 in C11.
    pose proof (AG3 12 ltac:(notin_list)) as C12. rewrite B12 in C12.
    pose proof (AG3 13 ltac:(notin_list)) as C13. rewrite B13 in C13.
    destruct (Z.le_gt_cases n 8) as [Hn8|Hn8].
    { (* [comment removed for export] *)
      exists r3. split; [|split; [exact C10 | chainC]].
      eapply finish; [| eapply msteps_trans; [exact S1 |
        eapply msteps_trans; [apply (p1_cont r1 _ A12 A14 ltac:(lia)) |
        eapply msteps_trans; [exact S2 |
        eapply msteps_trans; [apply (p2_cont r2 _ B12 B14 ltac:(lia)) |
        eapply msteps_trans; [exact S3 | apply (p3_ret r3 _ C1 C12 C15 Hn8)]]]]]].
      intros i; cbn [inzrP]; lia. }
    (* [comment removed for export] *)
    set (k := ((- d) mod 4)%Z). assert (Hk : ((- d) mod 4 = k)%Z) by reflexivity.
    set (t := ((n - k) mod 4)%Z). assert (Ht : ((n - k) mod 4 = t)%Z) by reflexivity.
    destruct (k_facts k Hk) as [Hk3 Hal4].
    destruct (t_facts k t Ht) as [Ht3 Hm].
    set (m4 := ((n - k) / 4)%Z) in Hm.
    pose (m := (4 * m4)%Z). assert (Hm4 : (m = 4 * m4)%Z) by reflexivity. rewrite <- Hm4 in Hm.
    set (e := ((d + k) mod 8)%Z). assert (He : ((d + k) mod 8 = e)%Z) by reflexivity.
    pose proof (e_facts k e Hal4 He) as He04.
    clearbody k t m4 m e.
    let l := lastl S3 in destruct (p4_run r3 l k t m C10 C11 C12 Hk Ht ltac:(lia) Hk3 Ht3 ltac:(lia))
      as (r4 & S4 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & AG4).
    rewrite C15 in D15.
    pose proof (AG4 1 ltac:(notin_list)) as D1. rewrite C1 in D1.
    destruct (Z.le_gt_cases m 8) as [Hm8|Hm8].
    { (* [comment removed for export] *)
      exists r4. split; [|split; [exact D10 | chainC]].
      eapply finish; [| eapply msteps_trans; [exact S1 |
        eapply msteps_trans; [apply (p1_cont r1 _ A12 A14 ltac:(lia)) |
        eapply msteps_trans; [exact S2 |
        eapply msteps_trans; [apply (p2_cont r2 _ B12 B14 ltac:(lia)) |
        eapply msteps_trans; [exact S3 |
        eapply msteps_trans; [apply (p3_cont r3 _ C12 C15 ltac:(lia)) |
        eapply msteps_trans; [exact S4 | apply (p4_ret r4 _ m D1 D14 D15 ltac:(lia))]]]]]]]].
      intros i; cbn [inzrP]; lia. }
    let l := lastl S4 in destruct (p5_run r4 l k m D11 D12 D13 ltac:(lia) ltac:(lia) ltac:(lia)) as (r5 & S5 & E15 & AG5).
    pose proof (AG5 1 ltac:(notin_list)) as E1. rewrite D1 in E1.
    pose proof (AG5 10 ltac:(notin_list)) as E10. rewrite D10 in E10.
    pose proof (AG5 11 ltac:(notin_list)) as E11. rewrite D11 in E11.
    pose proof (AG5 12 ltac:(notin_list)) as E12. rewrite D12 in E12.
    pose proof (AG5 13 ltac:(notin_list)) as E13. rewrite D13 in E13.
    pose proof (AG5 14 ltac:(notin_list)) as E14. rewrite D14 in E14.
    destruct (Z.le_gt_cases m 24) as [Hm24|Hm24].
    { (* [comment removed for export] *)
      exists r5. split; [|split; [exact E10 | chainC]].
      eapply finish; [| eapply msteps_trans; [exact S1 |
        eapply msteps_trans; [apply (p1_cont r1 _ A12 A14 ltac:(lia)) |
        eapply msteps_trans; [exact S2 |
        eapply msteps_trans; [apply (p2_cont r2 _ B12 B14 ltac:(lia)) |
        eapply msteps_trans; [exact S3 |
        eapply msteps_trans; [apply (p3_cont r3 _ C12 C15 ltac:(lia)) |
        eapply msteps_trans; [exact S4 |
        eapply msteps_trans; [apply (p4_cont r4 _ m D14 D15 ltac:(lia)) |
        eapply msteps_trans; [exact S5 | apply (p5_ret r5 _ m E1 E14 E15 ltac:(lia))]]]]]]]]]].
      intros i; cbn [inzrP]; lia. }
    let l := lastl S5 in destruct (p6_run r5 l k m e E11 E12 E13 E14 Hal4 He ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      as (r6 & S6 & F11 & F12 & F14 & F15 & F16 & AG6).
    pose proof (AG6 1 ltac:(notin_list)) as F1. rewrite E1 in F1.
    pose proof (AG6 10 ltac:(notin_list)) as F10. rewrite E10 in F10.
    destruct (Z.lt_ge_cases (m - 24 - e) 32) as [Hm2|Hm2].
    { (* [comment removed for export] *)
      exists r6. split; [|split; [exact F10 | chainC]].
      eapply finish; [| eapply msteps_trans; [exact S1 |
        eapply msteps_trans; [apply (p1_cont r1 _ A12 A14 ltac:(lia)) |
        eapply msteps_trans; [exact S2 |
        eapply msteps_trans; [apply (p2_cont r2 _ B12 B14 ltac:(lia)) |
        eapply msteps_trans; [exact S3 |
        eapply msteps_trans; [apply (p3_cont r3 _ C12 C15 ltac:(lia)) |
        eapply msteps_trans; [exact S4 |
        eapply msteps_trans; [apply (p4_cont r4 _ m D14 D15 ltac:(lia)) |
        eapply msteps_trans; [exact S5 |
        eapply msteps_trans; [apply (p5_cont r5 _ m E14 E15 ltac:(lia)) |
        eapply msteps_trans; [exact S6 | apply (p6_ret r6 _ (m - 24 - e) F1 F14 F16 ltac:(lia))]]]]]]]]]]]].
      intros i; cbn [inzrP]; lia. }
    (* [comment removed for export] *)
    let l := lastl S6 in destruct (p7_run r6 l k e (m - 24 - e) F11 F12 F14 F15 F16 ltac:(lia)) as (r7 & S7 & G11 & G12 & G13 & G14 & AG7).
    pose proof (AG7 1 ltac:(notin_list)) as G1. rewrite F1 in G1.
    pose proof (AG7 10 ltac:(notin_list)) as G10. rewrite F10 in G10.
    set (q := Z.to_nat ((m - 24 - e) / 32 - 1)).
    pose proof (q_facts (m - 24 - e) Hm2) as Hq. fold q in Hq. clearbody q.
    let l := lastl S7 in
    destruct (loop_run q r7 l (k + 24 + e) (k + 24 + e) (m - 24 - e) G1 G11 G12 G13 G14
                  ltac:(lia) ltac:(lia) Hq) as (r8 & S8 & AG8).
    pose proof (AG8 10 ltac:(notin_list)) as K10. rewrite G10 in K10.
    exists r8. split; [|split; [exact K10 | chainC]].
    eapply finish; [| eapply msteps_trans; [exact S1 |
      eapply msteps_trans; [apply (p1_cont r1 _ A12 A14 ltac:(lia)) |
      eapply msteps_trans; [exact S2 |
      eapply msteps_trans; [apply (p2_cont r2 _ B12 B14 ltac:(lia)) |
      eapply msteps_trans; [exact S3 |
      eapply msteps_trans; [apply (p3_cont r3 _ C12 C15 ltac:(lia)) |
      eapply msteps_trans; [exact S4 |
      eapply msteps_trans; [apply (p4_cont r4 _ m D14 D15 ltac:(lia)) |
      eapply msteps_trans; [exact S5 |
      eapply msteps_trans; [apply (p5_cont r5 _ m E14 E15 ltac:(lia)) |
      eapply msteps_trans; [exact S6 |
      eapply msteps_trans; [exact S7 | rewrite <- zf_drop_empty with (lo := (k + 24 + e)%Z); exact S8 ]]]]]]]]]]]]].
    intros i; cbn [inzrP]; lia.
  Qed.

End MS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Contract.
  Context {fx : FPState} {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL}.

  (* [comment removed for export] *)
  Theorem memset_spec : forall regs (M rom : word -> option byte) (d n : Z) (ret : word),
    (0 <= d)%Z -> (1 <= n < 2 ^ 64)%Z -> (d + n <= 2 ^ 64)%Z ->
    store_ok SEGS M (Z_to_bv 64 d) (Z.to_nat n) = true -> ret_ok ret ->
    getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 0 ->
    getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (rl dF_1cdb8 0x1cdb8) M rom) (mkst regs' ret (zf M d [(0, n)]%Z) rom)
      /\ getr regs' 10 = Z_to_bv 64 d
      /\ regs_agree (fun r => In r memset_clob) regs regs'.
  Proof.
    intros regs M rom d n ret Hd Hn Hdn Hok Hret H1 H10 H11 H12.
    exact (memset_run M d n rom ret Hd ltac:(lia) ltac:(lia) Hdn Hok Hret regs H1 H10 H11 H12).
  Qed.

  (* [comment removed for export] *)
  Lemma memset_post_mem : forall (M : word -> option byte) (d n : Z),
    (0 <= d)%Z -> (d + n <= 2 ^ 64)%Z ->
    (forall i, (0 <= i < n)%Z -> zf M d [(0, n)]%Z (Z_to_bv 64 (d + i)) = Some (Z_to_bv 8 0))
    /\ (forall x : word, (bv_unsigned x < d \/ d + n <= bv_unsigned x)%Z -> zf M d [(0, n)]%Z x = M x)
    /\ mem_grows M (zf M d [(0, n)]%Z).
  Proof.
    intros M d n Hd Hdn. split; [|split; [|apply zf_grows]].
    - intros i Hi. apply zf_inside. apply inzr_trueP. cbn [inzrP]. rewrite u_Z2bv by lia. lia.
    - intros x Hx. apply zf_outside. apply inzr_falseP. cbn [inzrP]. lia.
  Qed.

  (* [comment removed for export] *)
  Corollary memset_at : forall model regs (M rom : word -> option byte) (d n : Z) (ret : word) (S : TSet),
    md_pure model ->
    (0 <= d)%Z -> (1 <= n < 2 ^ 64)%Z -> (d + n <= 2 ^ 64)%Z ->
    store_ok SEGS M (Z_to_bv 64 d) (Z.to_nat n) = true -> ret_ok ret ->
    getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 0 ->
    getr regs 12 = Z_to_bv 64 n ->
    (forall regs', getr regs' 10 = Z_to_bv 64 d -> regs_agree (fun r => In r memset_clob) regs regs' ->
       realizes SEGS (mkCfg (mkst regs' ret (zf M d [(0, n)]%Z) rom) model) S) ->
    realizes SEGS (mkCfg (mkst regs (rl dF_1cdb8 0x1cdb8) M rom) model) S.
  Proof.
    intros model regs M rom d n ret S Hp Hd Hn Hdn Hok Hret H1 H10 H11 H12 HK.
    destruct (memset_spec regs M rom d n ret Hd Hn Hdn Hok Hret H1 H10 H11 H12) as (regs' & RUN & A10 & AG).
    eapply (rz_msteps SEGS); [exact (mp_halted _ Hp) | exact (mp_lazy _ Hp) | exact RUN |].
    apply HK; [exact A10 | exact AG].
  Qed.
End Contract.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
