(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic
  Ub0ExitBase Ub0_code_atexit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
Inductive axv : Type := AX0 | AXg.
Definition atexit_cells (mem : word -> option byte) (ax : axv) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0x90f84) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0))
  /\ match ax with
     | AX0 => rdn RSEGS mem (Z_to_bv 64 0x90f90) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
     | AXg => rdn RSEGS mem (Z_to_bv 64 0x90f90) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x90f98))
         /\ rdn RSEGS mem (Z_to_bv 64 0x90f88) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1))
         /\ rdn RSEGS mem (Z_to_bv 64 0x90f98) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
         /\ rdn RSEGS mem (Z_to_bv 64 0x90fa0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x4bf04))
         /\ rdn RSEGS mem (Z_to_bv 64 0x910a0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x20770))
     end.

(* [comment removed for export] *)
Lemma atexit_cells_frame : forall (M M' : word -> option byte) (ax : axv),
  (forall a : Z, ((0x90f80 <= a < 0x911a0))%Z -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> atexit_cells M ax -> atexit_cells M' ax.
Proof.
  intros M M' ax AG H.
  assert (R : forall (a : Z) (n : nat) v, (0 <= a)%Z -> (a + Z.of_nat n <= 0x911a0)%Z ->
             (forall x : Z, (a <= x < a + Z.of_nat n)%Z -> ((0x90f80 <= x < 0x911a0))%Z) -> rdn RSEGS M (Z_to_bv 64 a) n = v -> rdn RSEGS M' (Z_to_bv 64 a) n = v).
  { intros a n v H1 H2 HF <-. apply rdn_ext; [rewrite u_Z2bv by lia; lia|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
    rewrite <- (Z_to_bv_bv_unsigned 64 x). apply AG. apply HF. lia. }
  unfold atexit_cells in *. destruct H as (H0 & H).
  split; [apply R; [lia | cbn; lia | intros x Hx; cbn in Hx; lia | exact H0]|].
  destruct ax; repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end;
    repeat split; (apply R; [lia | cbn; lia | intros x Hx; cbn in Hx; lia | assumption]).
Qed.

Section FPX_1. Context {fx : PropExec.FPState}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ax_writes (ax : axv) (m : word -> option byte) : word -> option byte :=
  match ax with
  | AX0 => m
  | AXg => wbytes (wbytes (wbytes (wbytes (m)
      (Z_to_bv 64 0x90f88) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 0x90f88) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
      (Z_to_bv 64 0x90f88) (word_to_le_bytes 4 (Z_to_bv 64 32)))
      (Z_to_bv 64 0x90f90) (word_to_le_bytes 8 (Z_to_bv 64 0))
  end.
Definition mem_w1 (ax : axv) (mem : word -> option byte) (sp ra s0 : word) (tid : Z) (code s1 s2 s3 : word) :=
  wbytes (ax_writes ax (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (bv_unsigned sp - 16)) (word_to_le_bytes 8 s0))
    (Z_to_bv 64 0x911a0) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x4bfbc)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3)))
    (Z_to_bv 64 0x90f80) [Z_to_bv 8 1].

Lemma w1 : forall (ax : axv) regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn RSEGS mem (Z_to_bv 64 0x911a0) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  stdio_globals mem ->
  rdn RSEGS mem (Z_to_bv 64 0x703c4) 1%nat = Some [Z_to_bv 8 0] ->      (* [comment removed for export] *)
  atexit_cells mem ax ->
  exists regs',
    msteps RSEGS (mkst regs (0x4bf58 : word) mem rom)
                 (mkst regs' (0x4bf0c : word) (mem_w1 ax mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x4bfc0
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros ax regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock GL Mcb AX.
  destruct GL as (Gnl & _).
  destruct ax.
  { (* [comment removed for export] *)
    destruct AX as (Mxl & Mxh). unfold mem_w1, ax_writes. eexists. split.
    - (* [comment removed for export] *)
      stepn F_4bf58 D_4bf58. rewrite Hsp. sp_renorm.
      (* [comment removed for export] *)
      stepST F_4bf5c D_4bf5c (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
      stepST F_4bf60 D_4bf60 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
      (* [comment removed for export] *)
      stepn F_4bf64 D_4bf64.
      stepn F_4bf68 D_4bf68. rewrite Htp.
      (* [comment removed for export] *)
      stepLD F_4bf6c D_4bf6c (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
        ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      rewrite (v_lw_small tid) by lia.
      (* [comment removed for export] *)
      stepn F_4bf70 D_4bf70.
      stepn F_4bf74 D_4bf74.
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity
        | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
          [ exact F_4bf78 | reflexivity | exact D_4bf78
          | gres; u_norm; reflexivity
          | gres; rdn_by Mlock
          | apply bytes_le_to_Z_4; u_norm; lia ]
        | ].
      reduce_bv_eqb_ifs; norm_pc_r; vnorm.
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity
        | eapply step_bne_ft_r; [exact F_4bf7c | reflexivity | exact D_4bf7c | gres; cond_compute ] | ].
      norm_pc_r.
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity
        | eapply step_sc_w_ok; [exact F_4bf80 | reflexivity | exact D_4bf80
          | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
      step_simpl; vnorm.
      (* [comment removed for export] *)
      stepb_ft F_4bf84 D_4bf84 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepn F_4bf88 D_4bf88.
      (* [comment removed for export] *)
      stepb_ft F_4bf8c D_4bf8c ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
      (* [comment removed for export] *)
      stepb_tk F_4bf90 D_4bf90 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepn F_4bfb4 D_4bfb4. rewrite Ha0.
      (* [comment removed for export] *)
      stepn F_4bfb8 D_4bfb8.
      (* [comment removed for export] *)
      stepn F_4bd74 D_4bd74. sp_renorm.
      stepST F_4bd78 D_4bd78 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x4bfbc) ltac:(sok_stack SOK).
      stepST F_4bd7c D_4bd7c (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
      stepST F_4bd80 D_4bd80 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
      stepST F_4bd84 D_4bd84 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
      stepST F_4bd88 D_4bd88 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
      stepn F_4bd8c D_4bd8c. stepn F_4bd90 D_4bd90. stepn F_4bd94 D_4bd94. stepn F_4bd98 D_4bd98.
      (* [comment removed for export] *)
      stepn F_4bd9c D_4bd9c.
      stepn F_59d24 D_59d24.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_59d28 | reflexivity | exact D_59d28 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_59d2c D_59d2c ltac:(cond_compute).
      stepret F_59f1c D_59f1c (0x4bda0 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepLD F_4bda0 D_4bda0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_4bda4 D_4bda4 ltac:(cond_compute).
      stepn F_4be14 D_4be14.
      stepST F_4be18 D_4be18 (Z_to_bv 64 0x90f80) (Z_to_bv 64 1) ltac:(sok_data).
      change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
      stepn F_4be1c D_4be1c.
      stepLD8 F_4be20 D_4be20 (Z_to_bv 64 0x4bfbc).
      stepLD8 F_4be24 D_4be24 code.
      stepLD8 F_4be28 D_4be28 (getr regs 9).
      stepLD8 F_4be2c D_4be2c (getr regs 18).
      stepLD8 F_4be30 D_4be30 (getr regs 19).
      stepn F_4be34 D_4be34. sp_renorm.
      (* [comment removed for export] *)
      stepn F_4be38 D_4be38.
      stepLD F_59fac D_59fac (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_59fb0 D_59fb0 ltac:(cond_compute).
      stepret F_59fb4 D_59fb4 (0x4bfbc : word) ltac:(bveq).
      stepn F_4bfbc D_4bfbc.
      apply mst_refl.
    - repeat split; gres; try reflexivity. exact Htp. }
  { 
    destruct AX as (Mxl & Mxh & Msl & Mnx & Mf0 & Ma0). unfold mem_w1, ax_writes. eexists. split.
    - 
      stepn F_4bf58 D_4bf58. rewrite Hsp. sp_renorm.
      stepST F_4bf5c D_4bf5c (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
      stepST F_4bf60 D_4bf60 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
      stepn F_4bf64 D_4bf64.
      stepn F_4bf68 D_4bf68. rewrite Htp.
      stepLD F_4bf6c D_4bf6c (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
        ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      rewrite (v_lw_small tid) by lia.
      stepn F_4bf70 D_4bf70.
      stepn F_4bf74 D_4bf74.
      eapply mst_step; [reflexivity
        | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
          [ exact F_4bf78 | reflexivity | exact D_4bf78
          | gres; u_norm; reflexivity
          | gres; rdn_by Mlock
          | apply bytes_le_to_Z_4; u_norm; lia ]
        | ].
      reduce_bv_eqb_ifs; norm_pc_r; vnorm.
      eapply mst_step; [reflexivity
        | eapply step_bne_ft_r; [exact F_4bf7c | reflexivity | exact D_4bf7c | gres; cond_compute ] | ].
      norm_pc_r.
      eapply mst_step; [reflexivity
        | eapply step_sc_w_ok; [exact F_4bf80 | reflexivity | exact D_4bf80
          | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
      step_simpl; vnorm.
      stepb_ft F_4bf84 D_4bf84 ltac:(cond_compute).
      stepn F_4bf88 D_4bf88.
      stepb_ft F_4bf8c D_4bf8c ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
      stepb_tk F_4bf90 D_4bf90 ltac:(cond_compute).
      stepn F_4bfb4 D_4bfb4. rewrite Ha0.
      stepn F_4bfb8 D_4bfb8.
      stepn F_4bd74 D_4bd74. sp_renorm.
      stepST F_4bd78 D_4bd78 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x4bfbc) ltac:(sok_stack SOK).
      stepST F_4bd7c D_4bd7c (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
      stepST F_4bd80 D_4bd80 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
      stepST F_4bd84 D_4bd84 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
      stepST F_4bd88 D_4bd88 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
      stepn F_4bd8c D_4bd8c. stepn F_4bd90 D_4bd90. stepn F_4bd94 D_4bd94. stepn F_4bd98 D_4bd98.
      stepn F_4bd9c D_4bd9c.
      stepn F_59d24 D_59d24.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_59d28 | reflexivity | exact D_59d28 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_59d2c D_59d2c ltac:(cond_compute).
      stepret F_59f1c D_59f1c (0x4bda0 : word) ltac:(bveq).
      stepLD F_4bda0 D_4bda0 (word_to_le_bytes 8 (Z_to_bv 64 0x90f98)) (Z_to_bv 64 0x90f98) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_4bda4 D_4bda4 ltac:(cond_compute).
      stepLD F_4bda8 D_4bda8 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(addr_norm; rdn_by Msl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_4bdac D_4bdac.
      stepn F_4bdc4 D_4bdc4.
      stepST F_4bdc8 D_4bdc8 (Z_to_bv 64 0x90f88) (Z_to_bv 64 0) ltac:(sok_data).
      stepb_ft F_4bdcc D_4bdcc ltac:(cond_compute).
      stepLD F_4bdd0 D_4bdd0 (word_to_le_bytes 8 (Z_to_bv 64 0x90f98)) (Z_to_bv 64 0x90f98) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_4bdd4 D_4bdd4.
      stepn F_4bdd8 D_4bdd8.
      stepLD F_4bddc D_4bddc (word_to_le_bytes 8 (Z_to_bv 64 0x4bf04)) (Z_to_bv 64 0x4bf04) ltac:(addr_norm; rdn_by Mf0) ltac:(apply bytes_le_to_Z_8).
      stepLD F_4bde0 D_4bde0 (word_to_le_bytes 8 (Z_to_bv 64 0x20770)) (Z_to_bv 64 0x20770) ltac:(addr_norm; rdn_by Ma0) ltac:(apply bytes_le_to_Z_8).
      stepn F_4bde4 D_4bde4.
      stepn F_4bde8 D_4bde8.
      stepLD F_59fac D_59fac (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_59fb0 D_59fb0 ltac:(cond_compute).
      stepret F_59fb4 D_59fb4 (0x4bdec : word) ltac:(bveq).
      stepn F_4bdec D_4bdec.
      stepret F_4bdf0 D_4bdf0 (0x4bf04 : word) ltac:(bveq).
      stepret F_4bf04 D_4bf04 (0x20770 : word) ltac:(bveq).
      stepn F_20770 D_20770.
      stepLBU F_20774 D_20774 (Z_to_bv 8 0) ltac:(addr_norm; rdn_by Mcb).
      stepb_ft F_20778 D_20778 ltac:(cond_compute).
      stepret F_2077c D_2077c (0x4bdf4 : word) ltac:(bveq).
      stepn F_4bdf4 D_4bdf4.
      stepn F_4bdf8 D_4bdf8.
      stepn F_59d24 D_59d24.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_59d28 | reflexivity | exact D_59d28 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_59d2c D_59d2c ltac:(cond_compute).
      stepret F_59f1c D_59f1c (0x4bdfc : word) ltac:(bveq).
      stepLD F_4bdfc D_4bdfc (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_4be00 D_4be00.
      stepST F_4be04 D_4be04 (Z_to_bv 64 0x90f88) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
      stepb_ft F_4be08 D_4be08 ltac:(cond_compute).
      stepLD F_4be0c D_4be0c (word_to_le_bytes 8 (Z_to_bv 64 0x90f98)) (Z_to_bv 64 0x90f98) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_4be10 D_4be10.
      stepLD F_4bdb0 D_4bdb0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mnx) ltac:(apply bytes_le_to_Z_8).
      stepn F_4bdb4 D_4bdb4.
      stepST F_4bdb8 D_4bdb8 (Z_to_bv 64 0x90f88) (Z_to_bv 64 32) ltac:(sok_data).
      stepST F_4bdbc D_4bdbc (Z_to_bv 64 0x90f90) (Z_to_bv 64 0) ltac:(sok_data).
      stepb_tk F_4bdc0 D_4bdc0 ltac:(cond_compute).
      stepn F_4be14 D_4be14.
      stepST F_4be18 D_4be18 (Z_to_bv 64 0x90f80) (Z_to_bv 64 1) ltac:(sok_data).
      change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
      stepn F_4be1c D_4be1c.
      stepLD8 F_4be20 D_4be20 (Z_to_bv 64 0x4bfbc).
      stepLD8 F_4be24 D_4be24 code.
      stepLD8 F_4be28 D_4be28 (getr regs 9).
      stepLD8 F_4be2c D_4be2c (getr regs 18).
      stepLD8 F_4be30 D_4be30 (getr regs 19).
      stepn F_4be34 D_4be34. sp_renorm.
      stepn F_4be38 D_4be38.
      stepLD F_59fac D_59fac (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_59fb0 D_59fb0 ltac:(cond_compute).
      stepret F_59fb4 D_59fb4 (0x4bfbc : word) ltac:(bveq).
      stepn F_4bfbc D_4bfbc.
      apply mst_refl.
    - repeat split; gres; try reflexivity. exact Htp. }
Qed.

Definition mem_w2 (mem : word -> option byte) (sp code s1v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x4bfc0)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x4bf3c)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x5bce0)))
    (Z_to_bv 64 0x603b8) [Z_to_bv 8 1].

Lemma w2 : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x4bfc0 -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x5f0f0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x5bce8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5f0f8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x5bce0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5bce0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x202b8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x603b8) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x5efc0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x4be3c)) ->
  rdn RSEGS mem (Z_to_bv 64 0x60100) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x60100)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5efc8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x4bf0c : word) mem rom)
                 (mkst regs' (0x4ed20 : word) (mem_w2 mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x4bfc4
    /\ getr regs' 9 = s1v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hra Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mdso Mg2.
  unfold mem_w2. eexists. split.
  - 
    stepn F_4bf0c D_4bf0c. rewrite Hsp. sp_renorm.
    stepST F_4bf10 D_4bf10 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x4bfc0) ltac:(sok_stack SOK).
    stepST F_4bf14 D_4bf14 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_4bf18 D_4bf18 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    stepn F_4bf1c D_4bf1c.
    stepn F_4bf20 D_4bf20.
    stepLD8 F_4bf24 D_4bf24 (Z_to_bv 64 0x5bce8).
    stepLD8 F_4bf28 D_4bf28 (Z_to_bv 64 0x5bce0).
    stepb_ft F_4bf2c D_4bf2c ltac:(cond_compute).
    stepLD8 F_4bf30 D_4bf30 (Z_to_bv 64 0x202b8).
    stepn F_4bf34 D_4bf34.
    stepjr F_4bf38 D_4bf38 (Z_to_bv 64 0x202b8) ltac:(gres; reflexivity). vnorm.
    stepn F_202b8 D_202b8. sp_renorm.
    stepST F_202bc D_202bc (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x4bf3c) ltac:(sok_stack SOK).
    stepST F_202c0 D_202c0 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x5bce0) ltac:(sok_stack SOK).
    stepn F_202c4 D_202c4.
    stepn F_202c8 D_202c8.
    stepn F_202cc D_202cc.
    stepLBU F_202d0 D_202d0 (Z_to_bv 8 0) ltac:(rewrite v_addi_0; rdn_by Mcomp).
    stepn F_202d4 D_202d4.
    stepb_tk F_202d8 D_202d8 ltac:(cond_compute).
    stepn F_202e4 D_202e4.
    stepn F_202e8 D_202e8.
    stepn F_202ec D_202ec.
    stepST F_202f0 D_202f0 (Z_to_bv 64 0x603b8) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_202f4 D_202f4.
    stepLD8 F_202f8 D_202f8 (Z_to_bv 64 0x4be3c).
    stepb_ft F_202fc D_202fc ltac:(cond_compute).
    stepn F_20300 D_20300.
    stepn F_20304 D_20304.
    stepn F_20308 D_20308.
    stepLD8 F_2030c D_2030c (Z_to_bv 64 0x60100).
    stepn F_20310 D_20310.
    stepret F_4be3c D_4be3c (0x20314 : word) ltac:(bveq).
    stepn F_20314 D_20314.
    stepn F_20318 D_20318.
    stepLD8 F_2031c D_2031c (Z_to_bv 64 0).
    stepb_tk F_20320 D_20320 ltac:(cond_compute).
    stepLD8 F_20338 D_20338 (Z_to_bv 64 0x4bf3c).
    stepLD8 F_2033c D_2033c (Z_to_bv 64 0x5bce0).
    stepn F_20340 D_20340. sp_renorm.
    stepret F_20344 D_20344 (0x4bf3c : word) ltac:(bveq).
    stepn F_4bf3c D_4bf3c.
    stepb_ft F_4bf40 D_4bf40 ltac:(cond_compute).
    stepLD8 F_4bf44 D_4bf44 (Z_to_bv 64 0x4bfc0).
    stepLD8 F_4bf48 D_4bf48 code.
    stepLD8 F_4bf4c D_4bf4c s1v.
    stepn F_4bf50 D_4bf50. sp_renorm.
    stepn F_4bf54 D_4bf54.
    stepret F_4bf08 D_4bf08 (0x4bfc0 : word) ltac:(bveq).
    stepn F_4bfc0 D_4bfc0.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End FPX_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
