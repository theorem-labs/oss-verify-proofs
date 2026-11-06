(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import StartupTac RefMemcpyLib ShapeAlg PureModel.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib LeptArith.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require Import MemsetFillLib MemsetFill_iface.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14_code_28000_29000.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation memset_clob := memset_fill_clob (only parsing).

Section MS.
  Context {fx : FPState}.
  Variable M : word -> option byte.
  Variables d n c : Z.
  Hypothesis Hc : (0 <= c < 256)%Z.
  Variable rom : word -> option byte.
  Variable ret : word.
  Hypothesis Hd : (0 <= d)%Z.
  Hypothesis Hn : (1 <= n)%Z.
  Hypothesis Hn64 : (n < 2 ^ 64)%Z.
  Hypothesis Hdn : (d + n <= 2 ^ 64)%Z.
  Hypothesis Hok : store_ok SEGS M (Z_to_bv 64 d) (Z.to_nat n) = true.
  Hypothesis Hret : ret_ok ret.

  #[local] Abbreviation ZF l := (cf (Z_to_bv 8 c) M d l) (only parsing).

  (* [comment removed for export] *)
  Lemma ok_at : forall l o (w : nat), (0 <= o)%Z -> (o + Z.of_nat w <= n)%Z ->
    store_ok SEGS (ZF l) (Z_to_bv 64 (d + o)) w = true.
  Proof.
    intros l o w Ho Hw. apply store_ok_cf.
    destruct w as [|w']; [reflexivity|].
    eapply (store_ok_sub SEGS M (Z_to_bv 64 d) (Z_to_bv 64 (d + o)) (Z.to_nat n) (S w'));
      [ | exact Hok | | ]; rewrite ?u_Z2bv by lia; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma zst_sb : forall regs pc w rs1 rs2 (imm : bv 12) l e o,
    fetch_word SEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = Z_to_bv 64 e -> (e + bv_signed imm = d + o)%Z ->
    getr regs rs2 = Z_to_bv 64 c ->
    (0 <= o)%Z -> (o + 1 <= n)%Z ->
    RiscvSemantics.step SEGS (mkst regs pc (ZF l) rom) =
    MachineOk (mkst regs (v_addi pc 4) (ZF ((o, o + 1)%Z :: l)) rom).
  Proof.
    intros regs pc w rs1 rs2 imm l e o Hf He HD Hrs1 Heo Hrs2 Ho Hon.
    rewrite (MmapSim.step_sb_at SEGS regs pc (ZF l) rom w rs1 rs2 imm (Z_to_bv 64 (d + o)) (Z_to_bv 64 c) (Z_to_bv 8 c) Hf He HD).
    - f_equal. f_equal. change [Z_to_bv 8 c] with (repeat (Z_to_bv 8 c) 1). rewrite wbytes_cf by lia. reflexivity.
    - rewrite Hrs1, zbv_addi. f_equal. exact Heo.
    - exact Hrs2.
    - apply fill_sb; exact Hc.
    - apply (ok_at l o 1); lia.
  Qed.

  Lemma zst_sw : forall regs pc w rs1 rs2 (imm : bv 12) l e o,
    fetch_word SEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ4 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = Z_to_bv 64 e -> (e + bv_signed imm = d + o)%Z ->
    getr regs rs2 = Z_to_bv 64 (c * C32) ->
    (0 <= o)%Z -> (o + 4 <= n)%Z ->
    RiscvSemantics.step SEGS (mkst regs pc (ZF l) rom) =
    MachineOk (mkst regs (v_addi pc 4) (ZF ((o, o + 4)%Z :: l)) rom).
  Proof.
    intros regs pc w rs1 rs2 imm l e o Hf He HD Hrs1 Heo Hrs2 Ho Hon.
    rewrite (step_sw_at SEGS regs pc (ZF l) rom w rs1 rs2 imm (Z_to_bv 64 (d + o)) (Z_to_bv 64 (c * C32)) Hf He HD).
    - f_equal. f_equal. rewrite fill_sw by exact Hc. rewrite wbytes_cf by lia. reflexivity.
    - rewrite Hrs1, zbv_addi. f_equal. exact Heo.
    - exact Hrs2.
    - apply (ok_at l o 4); lia.
  Qed.

  Lemma zst_sd : forall regs pc w rs1 rs2 (imm : bv 12) l e o,
    fetch_word SEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ8 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = Z_to_bv 64 e -> (e + bv_signed imm = d + o)%Z ->
    getr regs rs2 = Z_to_bv 64 (c * C64) ->
    (0 <= o)%Z -> (o + 8 <= n)%Z ->
    RiscvSemantics.step SEGS (mkst regs pc (ZF l) rom) =
    MachineOk (mkst regs (v_addi pc 4) (ZF ((o, o + 8)%Z :: l)) rom).
  Proof.
    intros regs pc w rs1 rs2 imm l e o Hf He HD Hrs1 Heo Hrs2 Ho Hon.
    rewrite (step_sd_at SEGS regs pc (ZF l) rom w rs1 rs2 imm (Z_to_bv 64 (d + o)) (Z_to_bv 64 (c * C64)) Hf He HD).
    - f_equal. f_equal. rewrite fill_sd by exact Hc. rewrite wbytes_cf by lia. reflexivity.
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
    getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 c -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (0x2942c : word) (ZF []) rom)
                  (mkst regs' (0x29440 : word) (ZF [(n - 1, n - 1 + 1); (0, 0 + 1)]%Z) rom)
      /\ getr regs' 10 = Z_to_bv 64 d /\ getr regs' 11 = Z_to_bv 64 c /\ getr regs' 12 = Z_to_bv 64 n
      /\ getr regs' 13 = Z_to_bv 64 (d + n) /\ getr regs' 14 = Z_to_bv 64 3
      /\ regs_agree (fun r => In r memset_clob) regs regs'.
  Proof.
    intros regs H10 H11 H12.
    eexists. split.
    - stepb_ft F_28ef0 D_28ef0 ltac:(condZ).                 (* [comment removed for export] *)
      zst F_28ef4 D_28ef4 0%Z.                                (* [comment removed for export] *)
      zv F_28ef8 D_28ef8 (Z_to_bv 64 (d + n)).               (* [comment removed for export] *)
      sn F_28efc D_28efc.                                     (* [comment removed for export] *)
      zst F_28f00 D_28f00 (n - 1)%Z.                          (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.


  #[local] Abbreviation C := (fun r : reg => In r memset_clob) (only parsing).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma p1_ret : forall regs l,
    getr regs 1 = ret -> getr regs 12 = Z_to_bv 64 n -> getr regs 14 = Z_to_bv 64 3 -> (n <= 2)%Z ->
    msteps SEGS (mkst regs (0x29440 : word) (ZF l) rom) (mkst regs ret (ZF l) rom).
  Proof.
    intros regs l H1 H12 H14 Hle.
    stepb_tk F_28f04 D_28f04 ltac:(condZ).                   (* [comment removed for export] *)
    stepret F_28fe4 D_28fe4 ret ltac:(pin; reflexivity).
    apply mst_refl.
  Qed.

  Lemma p1_cont : forall regs l,
    getr regs 12 = Z_to_bv 64 n -> getr regs 14 = Z_to_bv 64 3 -> (3 <= n)%Z ->
    msteps SEGS (mkst regs (0x29440 : word) (ZF l) rom) (mkst regs (0x29444 : word) (ZF l) rom).
  Proof.
    intros regs l H12 H14 Hle.
    stepb_ft F_28f04 D_28f04 ltac:(condZ).
    apply mst_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma p2_run : forall regs l,
    getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 c -> getr regs 13 = Z_to_bv 64 (d + n) ->
    (3 <= n)%Z ->
    exists regs',
      msteps SEGS (mkst regs (0x29444 : word) (ZF l) rom)
                  (mkst regs' (0x29458 : word)
                        (ZF ((n - 2, n - 2 + 1) :: (n - 3, n - 3 + 1) :: (2, 2 + 1) :: (1, 1 + 1) :: l)%Z) rom)
      /\ getr regs' 14 = Z_to_bv 64 7
      /\ regs_agree (fun r : reg => In r [14]%list) regs regs'.
  Proof.
    intros regs l H10 H11 H13 Hn3.
    eexists. split.
    - zst F_28f08 D_28f08 1%Z.                                (* [comment removed for export] *)
      zst F_28f0c D_28f0c 2%Z.                                (* [comment removed for export] *)
      sn F_28f10 D_28f10.                                     (* [comment removed for export] *)
      zst F_28f14 D_28f14 (n - 3)%Z.                          (* [comment removed for export] *)
      zst F_28f18 D_28f18 (n - 2)%Z.                          (* [comment removed for export] *)
      apply mst_refl.
    - split; [gres; reflexivity | solve_regs_agree].
  Qed.

  Lemma p2_ret : forall regs l,
    getr regs 1 = ret -> getr regs 12 = Z_to_bv 64 n -> getr regs 14 = Z_to_bv 64 7 -> (n <= 6)%Z ->
    msteps SEGS (mkst regs (0x29458 : word) (ZF l) rom) (mkst regs ret (ZF l) rom).
  Proof.
    intros regs l H1 H12 H14 Hle.
    stepb_tk F_28f1c D_28f1c ltac:(condZ).
    stepret F_28fe4 D_28fe4 ret ltac:(pin; reflexivity).
    apply mst_refl.
  Qed.

  Lemma p2_cont : forall regs l,
    getr regs 12 = Z_to_bv 64 n -> getr regs 14 = Z_to_bv 64 7 -> (7 <= n)%Z ->
    msteps SEGS (mkst regs (0x29458 : word) (ZF l) rom) (mkst regs (0x2945c : word) (ZF l) rom).
  Proof.
    intros regs l H12 H14 Hle.
    stepb_ft F_28f1c D_28f1c ltac:(condZ).
    apply mst_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma p3_run : forall regs l,
    getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 c -> getr regs 13 = Z_to_bv 64 (d + n) ->
    (7 <= n)%Z ->
    exists regs',
      msteps SEGS (mkst regs (0x2945c : word) (ZF l) rom)
                  (mkst regs' (0x29468 : word) (ZF ((n - 4, n - 4 + 1) :: (3, 3 + 1) :: l)%Z) rom)
      /\ getr regs' 15 = Z_to_bv 64 9
      /\ regs_agree (fun r : reg => In r [15]%list) regs regs'.
  Proof.
    intros regs l H10 H11 H13 Hn7.
    eexists. split.
    - zst F_28f20 D_28f20 3%Z.                                (* [comment removed for export] *)
      sn F_28f24 D_28f24.                                     (* [comment removed for export] *)
      zst F_28f28 D_28f28 (n - 4)%Z.                          (* [comment removed for export] *)
      apply mst_refl.
    - split; [gres; reflexivity | solve_regs_agree].
  Qed.

  Lemma p3_ret : forall regs l,
    getr regs 1 = ret -> getr regs 12 = Z_to_bv 64 n -> getr regs 15 = Z_to_bv 64 9 -> (n <= 8)%Z ->
    msteps SEGS (mkst regs (0x29468 : word) (ZF l) rom) (mkst regs ret (ZF l) rom).
  Proof.
    intros regs l H1 H12 H15 Hle.
    stepb_tk F_28f2c D_28f2c ltac:(condZ).
    stepret F_28fe4 D_28fe4 ret ltac:(pin; reflexivity).
    apply mst_refl.
  Qed.

  Lemma p3_cont : forall regs l,
    getr regs 12 = Z_to_bv 64 n -> getr regs 15 = Z_to_bv 64 9 -> (9 <= n)%Z ->
    msteps SEGS (mkst regs (0x29468 : word) (ZF l) rom) (mkst regs (0x2946c : word) (ZF l) rom).
  Proof.
    intros regs l H12 H15 Hle.
    stepb_ft F_28f2c D_28f2c ltac:(condZ).
    apply mst_refl.
  Qed.


  (* [comment removed for export] *)
  Lemma p4_run : forall regs l k t m,
    getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 c -> getr regs 12 = Z_to_bv 64 n ->
    ((- d) mod 4 = k)%Z -> ((n - k) mod 4 = t)%Z -> (m = n - k - t)%Z ->
    (0 <= k <= 3)%Z -> (0 <= t <= 3)%Z -> (9 <= n)%Z ->
    exists regs',
      msteps SEGS (mkst regs (0x2946c : word) (ZF l) rom)
                  (mkst regs' (0x294a0 : word) (ZF ((k + m - 4, k + m - 4 + 4) :: (k, k + 4) :: l)%Z) rom)
      /\ getr regs' 10 = Z_to_bv 64 d /\ getr regs' 11 = Z_to_bv 64 (d + k) /\ getr regs' 12 = Z_to_bv 64 (c * C32)
      /\ getr regs' 13 = Z_to_bv 64 (d + k + m) /\ getr regs' 14 = Z_to_bv 64 m
      /\ getr regs' 15 = getr regs 15 /\ getr regs' 16 = Z_to_bv 64 (c * 2 ^ 56)
      /\ regs_agree C regs regs'.
  Proof.
    intros regs l k t m H10 H11 H12 Hk Ht Hm Hk3 Ht3 Hn9.
    eexists. split.
    - sn F_28f30 D_28f30.                                     (* [comment removed for export] *)
      stepiv F_28f34 D_28f34 (Z_to_bv 64 (c * 2 ^ 56)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; reflexivity).   (* [comment removed for export] *)
      sn F_28f38 D_28f38.                                     (* [comment removed for export] *)
      stepiv F_28f3c D_28f3c (Z_to_bv 64 k)
        ltac:(gres; pin; rewrite negw_and3, (u_Z2bv d) by lia; f_equal; exact Hk).   (* [comment removed for export] *)
      sn F_28f40 D_28f40.                                     (* [comment removed for export] *)
      zv F_28f44 D_28f44 (Z_to_bv 64 (n - k)).               (* [comment removed for export] *)
      zv F_28f48 D_28f48 (Z_to_bv 64 (d + k)).               (* [comment removed for export] *)
      sn F_28f4c D_28f4c.                                     (* [comment removed for export] *)
      stepiv F_28f50 D_28f50 (Z_to_bv 64 m)
        ltac:(gres; pin; imm_norm; rewrite andi_m4, !(u_Z2bv (n - k)) by lia; f_equal; lia).   (* [comment removed for export] *)
      sn F_28f54 D_28f54. fixv (Z_to_bv 64 (c * C32)) ltac:(apply fill_mulhu; exact Hc).   (* [comment removed for export] *)
      zst F_28f58 D_28f58 k.                                  (* [comment removed for export] *)
      zv F_28f5c D_28f5c (Z_to_bv 64 (d + k + m)).           (* [comment removed for export] *)
      zst F_28f60 D_28f60 (k + m - 4)%Z.                      (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma p4_ret : forall regs l m,
    getr regs 1 = ret -> getr regs 14 = Z_to_bv 64 m -> getr regs 15 = Z_to_bv 64 9 ->
    (0 <= m <= 8)%Z ->
    msteps SEGS (mkst regs (0x294a0 : word) (ZF l) rom) (mkst regs ret (ZF l) rom).
  Proof.
    intros regs l m H1 H14 H15 Hle.
    stepb_tk F_28f64 D_28f64 ltac:(condZ).
    stepret F_28fe4 D_28fe4 ret ltac:(pin; reflexivity).
    apply mst_refl.
  Qed.

  Lemma p4_cont : forall regs l m,
    getr regs 14 = Z_to_bv 64 m -> getr regs 15 = Z_to_bv 64 9 -> (9 <= m <= n)%Z ->
    msteps SEGS (mkst regs (0x294a0 : word) (ZF l) rom) (mkst regs (0x294a4 : word) (ZF l) rom).
  Proof.
    intros regs l m H14 H15 Hle.
    stepb_ft F_28f64 D_28f64 ltac:(condZ).
    apply mst_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma p5_run : forall regs l k m,
    getr regs 11 = Z_to_bv 64 (d + k) -> getr regs 12 = Z_to_bv 64 (c * C32) -> getr regs 13 = Z_to_bv 64 (d + k + m) ->
    (0 <= k)%Z -> (12 <= m)%Z -> (k + m <= n)%Z ->
    exists regs',
      msteps SEGS (mkst regs (0x294a4 : word) (ZF l) rom)
                  (mkst regs' (0x294b8 : word)
                     (ZF ((k + m - 8, k + m - 8 + 4) :: (k + m - 12, k + m - 12 + 4)
                          :: (k + 8, k + 8 + 4) :: (k + 4, k + 4 + 4) :: l)%Z) rom)
      /\ getr regs' 15 = Z_to_bv 64 25
      /\ regs_agree (fun r : reg => In r [15]%list) regs regs'.
  Proof.
    intros regs l k m H11 H12 H13 Hk Hm Hkm.
    eexists. split.
    - zst F_28f68 D_28f68 (k + 4)%Z.                          (* [comment removed for export] *)
      zst F_28f6c D_28f6c (k + 8)%Z.                          (* [comment removed for export] *)
      sn F_28f70 D_28f70.                                     (* [comment removed for export] *)
      zst F_28f74 D_28f74 (k + m - 12)%Z.                     (* [comment removed for export] *)
      zst F_28f78 D_28f78 (k + m - 8)%Z.                      (* [comment removed for export] *)
      apply mst_refl.
    - split; [gres; reflexivity | solve_regs_agree].
  Qed.

  Lemma p5_ret : forall regs l m,
    getr regs 1 = ret -> getr regs 14 = Z_to_bv 64 m -> getr regs 15 = Z_to_bv 64 25 ->
    (0 <= m <= 24)%Z ->
    msteps SEGS (mkst regs (0x294b8 : word) (ZF l) rom) (mkst regs ret (ZF l) rom).
  Proof.
    intros regs l m H1 H14 H15 Hle.
    stepb_tk F_28f7c D_28f7c ltac:(condZ).
    stepret F_28fe4 D_28fe4 ret ltac:(pin; reflexivity).
    apply mst_refl.
  Qed.

  Lemma p5_cont : forall regs l m,
    getr regs 14 = Z_to_bv 64 m -> getr regs 15 = Z_to_bv 64 25 -> (25 <= m <= n)%Z ->
    msteps SEGS (mkst regs (0x294b8 : word) (ZF l) rom) (mkst regs (0x294bc : word) (ZF l) rom).
  Proof.
    intros regs l m H14 H15 Hle.
    stepb_ft F_28f7c D_28f7c ltac:(condZ).
    apply mst_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma p6_run : forall regs l k m e,
    getr regs 11 = Z_to_bv 64 (d + k) -> getr regs 12 = Z_to_bv 64 (c * C32) -> getr regs 13 = Z_to_bv 64 (d + k + m) ->
    getr regs 14 = Z_to_bv 64 m ->
    ((d + k) mod 4 = 0)%Z -> ((d + k) mod 8 = e)%Z -> (0 <= e <= 4)%Z ->
    (0 <= k)%Z -> (28 <= m)%Z -> (k + m <= n)%Z ->
    exists regs',
      msteps SEGS (mkst regs (0x294bc : word) (ZF l) rom)
                  (mkst regs' (0x294ec : word)
                     (ZF ((k + m - 16, k + m - 16 + 4) :: (k + m - 20, k + m - 20 + 4)
                          :: (k + m - 24, k + m - 24 + 4) :: (k + m - 28, k + m - 28 + 4)
                          :: (k + 24, k + 24 + 4) :: (k + 20, k + 20 + 4)
                          :: (k + 16, k + 16 + 4) :: (k + 12, k + 12 + 4) :: l)%Z) rom)
      /\ getr regs' 11 = Z_to_bv 64 (d + k) /\ getr regs' 12 = Z_to_bv 64 (c * C32)
      /\ getr regs' 14 = Z_to_bv 64 (m - 24 - e) /\ getr regs' 15 = Z_to_bv 64 (24 + e)
      /\ getr regs' 16 = Z_to_bv 64 32
      /\ regs_agree (fun r : reg => In r [14; 15; 16]%list) regs regs'.
  Proof.
    intros regs l k m e H11 H12 H13 H14 Hal4 He He4 Hk Hm Hkm.
    eexists. split.
    - zst F_28f80 D_28f80 (k + 12)%Z.                         (* [comment removed for export] *)
      zst F_28f84 D_28f84 (k + 16)%Z.                         (* [comment removed for export] *)
      zst F_28f88 D_28f88 (k + 20)%Z.                         (* [comment removed for export] *)
      zst F_28f8c D_28f8c (k + 24)%Z.                         (* [comment removed for export] *)
      stepiv F_28f90 D_28f90 (Z_to_bv 64 e)
        ltac:(gres; pin; imm_norm; rewrite andi_4_al4 by (rewrite (u_Z2bv (d + k)) by lia; exact Hal4);
              rewrite (u_Z2bv (d + k)) by lia; f_equal; exact He).      (* [comment removed for export] *)
      sn F_28f94 D_28f94.                                     (* [comment removed for export] *)
      zv F_28f98 D_28f98 (Z_to_bv 64 (24 + e)).              (* [comment removed for export] *)
      zv F_28f9c D_28f9c (Z_to_bv 64 (m - 24 - e)).          (* [comment removed for export] *)
      zst F_28fa0 D_28fa0 (k + m - 28)%Z.                     (* [comment removed for export] *)
      zst F_28fa4 D_28fa4 (k + m - 24)%Z.                     (* [comment removed for export] *)
      zst F_28fa8 D_28fa8 (k + m - 20)%Z.                     (* [comment removed for export] *)
      zst F_28fac D_28fac (k + m - 16)%Z.                     (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma p6_ret : forall regs l m2,
    getr regs 1 = ret -> getr regs 14 = Z_to_bv 64 m2 -> getr regs 16 = Z_to_bv 64 32 ->
    (0 <= m2 < 32)%Z ->
    msteps SEGS (mkst regs (0x294ec : word) (ZF l) rom) (mkst regs ret (ZF l) rom).
  Proof.
    intros regs l m2 H1 H14 H16 Hle.
    stepb_tk F_28fb0 D_28fb0 ltac:(condZ).
    stepret F_28fe4 D_28fe4 ret ltac:(pin; reflexivity).
    apply mst_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma p7_run : forall regs l k e m2,
    getr regs 11 = Z_to_bv 64 (d + k) -> getr regs 12 = Z_to_bv 64 (c * C32) ->
    getr regs 14 = Z_to_bv 64 m2 -> getr regs 15 = Z_to_bv 64 (24 + e) -> getr regs 16 = Z_to_bv 64 32 ->
    (32 <= m2 <= n)%Z ->
    exists regs',
      msteps SEGS (mkst regs (0x294ec : word) (ZF l) rom) (mkst regs' (0x29504 : word) (ZF l) rom)
      /\ getr regs' 11 = Z_to_bv 64 (d + (k + 24 + e)) /\ getr regs' 12 = Z_to_bv 64 (c * C64)
      /\ getr regs' 13 = Z_to_bv 64 31 /\ getr regs' 14 = Z_to_bv 64 m2
      /\ regs_agree (fun r : reg => In r [11; 12; 13]%list) regs regs'.
  Proof.
    intros regs l k e m2 H11 H12 H14 H15 H16 Hm2.
    eexists. split.
    - stepb_ft F_28fb0 D_28fb0 ltac:(condZ).                 (* [comment removed for export] *)
      stepiv F_28fb4 D_28fb4 (Z_to_bv 64 (c * C32 * 2 ^ 32)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; reflexivity).   (* [comment removed for export] *)
      zv F_28fb8 D_28fb8 (Z_to_bv 64 (d + (k + 24 + e))).   (* [comment removed for export] *)
      stepiv F_28fbc D_28fbc (Z_to_bv 64 (c * C32))
        ltac:(gres; pin; imm_norm; rewrite zbv_srli by (unfold C32; lia); f_equal; apply Z.div_mul; lia).   (* [comment removed for export] *)
      sn F_28fc0 D_28fc0. fixv (Z_to_bv 64 (c * C64)) ltac:(apply fill_or64; exact Hc).   (* [comment removed for export] *)
      sn F_28fc4 D_28fc4.                                     (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma zf_merge32 : forall o0 o l, (o0 <= o)%Z ->
    ZF ((o + 24, o + 24 + 8) :: (o + 16, o + 16 + 8) :: (o + 8, o + 8 + 8) :: (o, o + 8) :: (o0, o) :: l)%Z
    = ZF ((o0, o + 32)%Z :: l).
  Proof. intros o0 o l Ho. apply cf_ext. intros i. inzr_tac. Qed.

  (* [comment removed for export] *)
  Lemma loop_run : forall q regs l o0 o r,
    getr regs 1 = ret -> getr regs 11 = Z_to_bv 64 (d + o) -> getr regs 12 = Z_to_bv 64 (c * C64) ->
    getr regs 13 = Z_to_bv 64 31 -> getr regs 14 = Z_to_bv 64 r ->
    (0 <= o0 <= o)%Z -> (o + r <= n)%Z ->
    (32 * (Z.of_nat q + 1) <= r < 32 * (Z.of_nat q + 1) + 32)%Z ->
    exists regs',
      msteps SEGS (mkst regs (0x29504 : word) (ZF ((o0, o) :: l)) rom)
                  (mkst regs' ret (ZF ((o0, o + 32 * (Z.of_nat q + 1))%Z :: l)) rom)
      /\ regs_agree (fun r : reg => In r [11; 14]%list) regs regs'.
  Proof.
    induction q as [|q IH]; intros regs l o0 o r H1 H11 H12 H13 H14 Ho Hor Hq.
    - eexists. split.
      + zst F_28fc8 D_28fc8 o.                                (* [comment removed for export] *)
        zst F_28fcc D_28fcc (o + 8)%Z.                        (* [comment removed for export] *)
        zst F_28fd0 D_28fd0 (o + 16)%Z.                       (* [comment removed for export] *)
        zst F_28fd4 D_28fd4 (o + 24)%Z.                       (* [comment removed for export] *)
        zv F_28fd8 D_28fd8 (Z_to_bv 64 (r - 32)).             (* [comment removed for export] *)
        zv F_28fdc D_28fdc (Z_to_bv 64 (d + (o + 32))).       (* [comment removed for export] *)
        stepb_ft F_28fe0 D_28fe0 ltac:(condZ).               (* [comment removed for export] *)
        stepret F_28fe4 D_28fe4 ret ltac:(pin; reflexivity).
        rewrite zf_merge32 by lia.
        replace (o + 32 * (Z.of_nat 0 + 1))%Z with (o + 32)%Z by lia.
        apply mst_refl.
      + solve_regs_agree.
    - eapply (runs_trans SEGS _ (fun rg => mkst rg (0x29504 : word) (ZF ((o0, o + 32)%Z :: l)) rom)
               (fun rg => getr rg 1 = ret /\ getr rg 11 = Z_to_bv 64 (d + (o + 32)) /\ getr rg 12 = Z_to_bv 64 (c * C64)
                          /\ getr rg 13 = Z_to_bv 64 31 /\ getr rg 14 = Z_to_bv 64 (r - 32)
                          /\ regs_agree (fun r : reg => In r [11; 14]%list) regs rg)).
      + eexists. split.
        * zst F_28fc8 D_28fc8 o.
          zst F_28fcc D_28fcc (o + 8)%Z.
          zst F_28fd0 D_28fd0 (o + 16)%Z.
          zst F_28fd4 D_28fd4 (o + 24)%Z.
          zv F_28fd8 D_28fd8 (Z_to_bv 64 (r - 32)).
          zv F_28fdc D_28fdc (Z_to_bv 64 (d + (o + 32))).
          stepb_tk F_28fe0 D_28fe0 ltac:(condZ).             (* [comment removed for export] *)
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
    msteps SEGS (mkst regs (0x2942c : word) (ZF []) rom) (mkst regs' ret (ZF L) rom) ->
    msteps SEGS (mkst regs (0x2942c : word) M rom) (mkst regs' ret (ZF [(0, n)]%Z) rom).
  Proof.
    intros regs regs' L HL HR. rewrite <- (cf_extP (Z_to_bv 8 c) M d L [(0, n)]%Z HL).
    rewrite cf_nil in HR. exact HR.
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
  Ltac lastl S := match type of S with msteps _ _ (mkst _ _ (cf _ _ _ ?l) _) => constr:(l) end.

  Theorem memset_run : forall regs,
    getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 c -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (0x2942c : word) M rom) (mkst regs' ret (ZF [(0, n)]%Z) rom)
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
      eapply msteps_trans; [exact S7 | rewrite <- cf_drop_empty with (lo := (k + 24 + e)%Z); exact S8 ]]]]]]]]]]]]].
    intros i; cbn [inzrP]; lia.
  Qed.

End MS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Contract.
  Context {fx : FPState}.

  Theorem memset_fill_o14 : memset_fill_stmt SEGS (0x2942c : word).
  Proof.
    unfold memset_fill_stmt. intros regs M rom d n c ret Hd Hn Hdn Hc Hok Hret H1 H10 H11 H12.
    destruct (memset_run M d n c Hc rom ret Hd ltac:(lia) ltac:(lia) Hdn Hok Hret regs H1 H10 H11 H12) as (regs' & RUN & A10 & AG).
    exists regs', (cf (Z_to_bv 8 c) M d [(0, n)]%Z). split; [exact RUN|]. split; [exact A10|]. split; [exact AG|].
    split; [|split; [apply cf_grows|]].
    - intros x Hx. apply cf_outside. apply inzr_falseP. cbn [inzrP]. lia.
    - intros i Hi. rewrite cf_inside; [discriminate|]. apply inzr_trueP. cbn [inzrP]. rewrite u_Z2bv by lia. lia.
  Qed.
End Contract.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
