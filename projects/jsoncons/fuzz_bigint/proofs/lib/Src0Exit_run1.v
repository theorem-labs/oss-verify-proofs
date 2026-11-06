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
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic
  Src0ExitBase Src0_code_atexit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
Inductive axv : Type := AX0 | AXg.
Definition atexit_cells (mem : word -> option byte) (ax : axv) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0x90484) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0))
  /\ match ax with
     | AX0 => rdn RSEGS mem (Z_to_bv 64 0x90490) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
     | AXg => rdn RSEGS mem (Z_to_bv 64 0x90490) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x90498))
         /\ rdn RSEGS mem (Z_to_bv 64 0x90488) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1))
         /\ rdn RSEGS mem (Z_to_bv 64 0x90498) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
         /\ rdn RSEGS mem (Z_to_bv 64 0x904a0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x4b408))
         /\ rdn RSEGS mem (Z_to_bv 64 0x905a0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x20520))
     end.

(* [comment removed for export] *)
Lemma atexit_cells_frame : forall (M M' : word -> option byte) (ax : axv),
  (forall a : Z, ((0x90480 <= a < 0x906a0))%Z -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> atexit_cells M ax -> atexit_cells M' ax.
Proof.
  intros M M' ax AG H.
  assert (R : forall (a : Z) (n : nat) v, (0 <= a)%Z -> (a + Z.of_nat n <= 0x906a0)%Z ->
             (forall x : Z, (a <= x < a + Z.of_nat n)%Z -> ((0x90480 <= x < 0x906a0))%Z) -> rdn RSEGS M (Z_to_bv 64 a) n = v -> rdn RSEGS M' (Z_to_bv 64 a) n = v).
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
      (Z_to_bv 64 0x90488) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 0x90488) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
      (Z_to_bv 64 0x90488) (word_to_le_bytes 4 (Z_to_bv 64 32)))
      (Z_to_bv 64 0x90490) (word_to_le_bytes 8 (Z_to_bv 64 0))
  end.
Definition mem_w1 (ax : axv) (mem : word -> option byte) (sp ra s0 : word) (tid : Z) (code s1 s2 s3 : word) :=
  wbytes (ax_writes ax (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (bv_unsigned sp - 16)) (word_to_le_bytes 8 s0))
    (Z_to_bv 64 0x906a0) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x4b4c0)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3)))
    (Z_to_bv 64 0x90480) [Z_to_bv 8 1].

Lemma w1 : forall (ax : axv) regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn RSEGS mem (Z_to_bv 64 0x906a0) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  stdio_globals mem ->
  rdn RSEGS mem (Z_to_bv 64 0x6f8c4) 1%nat = Some [Z_to_bv 8 0] ->      (* [comment removed for export] *)
  atexit_cells mem ax ->
  exists regs',
    msteps RSEGS (mkst regs (0x4b45c : word) mem rom)
                 (mkst regs' (0x4b410 : word) (mem_w1 ax mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x4b4c4
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros ax regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock GL Mcb AX.
  destruct GL as (Gnl & _).
  destruct ax.
  { (* [comment removed for export] *)
    destruct AX as (Mxl & Mxh). unfold mem_w1, ax_writes. eexists. split.
    - (* [comment removed for export] *)
      stepn F_4b45c D_4b45c. rewrite Hsp. sp_renorm.
      (* [comment removed for export] *)
      stepST F_4b460 D_4b460 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
      stepST F_4b464 D_4b464 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
      (* [comment removed for export] *)
      stepn F_4b468 D_4b468.
      stepn F_4b46c D_4b46c. rewrite Htp.
      (* [comment removed for export] *)
      stepLD F_4b470 D_4b470 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
        ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      rewrite (v_lw_small tid) by lia.
      (* [comment removed for export] *)
      stepn F_4b474 D_4b474.
      stepn F_4b478 D_4b478.
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity
        | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
          [ exact F_4b47c | reflexivity | exact D_4b47c
          | gres; u_norm; reflexivity
          | gres; rdn_by Mlock
          | apply bytes_le_to_Z_4; u_norm; lia ]
        | ].
      reduce_bv_eqb_ifs; norm_pc_r; vnorm.
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity
        | eapply step_bne_ft_r; [exact F_4b480 | reflexivity | exact D_4b480 | gres; cond_compute ] | ].
      norm_pc_r.
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity
        | eapply step_sc_w_ok; [exact F_4b484 | reflexivity | exact D_4b484
          | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
      step_simpl; vnorm.
      (* [comment removed for export] *)
      stepb_ft F_4b488 D_4b488 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepn F_4b48c D_4b48c.
      (* [comment removed for export] *)
      stepb_ft F_4b490 D_4b490 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
      (* [comment removed for export] *)
      stepb_tk F_4b494 D_4b494 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepn F_4b4b8 D_4b4b8. rewrite Ha0.
      (* [comment removed for export] *)
      stepn F_4b4bc D_4b4bc.
      (* [comment removed for export] *)
      stepn F_4b278 D_4b278. sp_renorm.
      stepST F_4b27c D_4b27c (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x4b4c0) ltac:(sok_stack SOK).
      stepST F_4b280 D_4b280 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
      stepST F_4b284 D_4b284 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
      stepST F_4b288 D_4b288 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
      stepST F_4b28c D_4b28c (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
      stepn F_4b290 D_4b290. stepn F_4b294 D_4b294. stepn F_4b298 D_4b298. stepn F_4b29c D_4b29c.
      (* [comment removed for export] *)
      stepn F_4b2a0 D_4b2a0.
      stepn F_59228 D_59228.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_5922c | reflexivity | exact D_5922c | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_59230 D_59230 ltac:(cond_compute).
      stepret F_59420 D_59420 (0x4b2a4 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepLD F_4b2a4 D_4b2a4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_4b2a8 D_4b2a8 ltac:(cond_compute).
      stepn F_4b318 D_4b318.
      stepST F_4b31c D_4b31c (Z_to_bv 64 0x90480) (Z_to_bv 64 1) ltac:(sok_data).
      change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
      stepn F_4b320 D_4b320.
      stepLD8 F_4b324 D_4b324 (Z_to_bv 64 0x4b4c0).
      stepLD8 F_4b328 D_4b328 code.
      stepLD8 F_4b32c D_4b32c (getr regs 9).
      stepLD8 F_4b330 D_4b330 (getr regs 18).
      stepLD8 F_4b334 D_4b334 (getr regs 19).
      stepn F_4b338 D_4b338. sp_renorm.
      (* [comment removed for export] *)
      stepn F_4b33c D_4b33c.
      stepLD F_594b0 D_594b0 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_594b4 D_594b4 ltac:(cond_compute).
      stepret F_594b8 D_594b8 (0x4b4c0 : word) ltac:(bveq).
      stepn F_4b4c0 D_4b4c0.
      apply mst_refl.
    - repeat split; gres; try reflexivity. exact Htp. }
  { 
    destruct AX as (Mxl & Mxh & Msl & Mnx & Mf0 & Ma0). unfold mem_w1, ax_writes. eexists. split.
    - 
      stepn F_4b45c D_4b45c. rewrite Hsp. sp_renorm.
      stepST F_4b460 D_4b460 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
      stepST F_4b464 D_4b464 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
      stepn F_4b468 D_4b468.
      stepn F_4b46c D_4b46c. rewrite Htp.
      stepLD F_4b470 D_4b470 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
        ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      rewrite (v_lw_small tid) by lia.
      stepn F_4b474 D_4b474.
      stepn F_4b478 D_4b478.
      eapply mst_step; [reflexivity
        | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
          [ exact F_4b47c | reflexivity | exact D_4b47c
          | gres; u_norm; reflexivity
          | gres; rdn_by Mlock
          | apply bytes_le_to_Z_4; u_norm; lia ]
        | ].
      reduce_bv_eqb_ifs; norm_pc_r; vnorm.
      eapply mst_step; [reflexivity
        | eapply step_bne_ft_r; [exact F_4b480 | reflexivity | exact D_4b480 | gres; cond_compute ] | ].
      norm_pc_r.
      eapply mst_step; [reflexivity
        | eapply step_sc_w_ok; [exact F_4b484 | reflexivity | exact D_4b484
          | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
      step_simpl; vnorm.
      stepb_ft F_4b488 D_4b488 ltac:(cond_compute).
      stepn F_4b48c D_4b48c.
      stepb_ft F_4b490 D_4b490 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
      stepb_tk F_4b494 D_4b494 ltac:(cond_compute).
      stepn F_4b4b8 D_4b4b8. rewrite Ha0.
      stepn F_4b4bc D_4b4bc.
      stepn F_4b278 D_4b278. sp_renorm.
      stepST F_4b27c D_4b27c (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x4b4c0) ltac:(sok_stack SOK).
      stepST F_4b280 D_4b280 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
      stepST F_4b284 D_4b284 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
      stepST F_4b288 D_4b288 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
      stepST F_4b28c D_4b28c (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
      stepn F_4b290 D_4b290. stepn F_4b294 D_4b294. stepn F_4b298 D_4b298. stepn F_4b29c D_4b29c.
      stepn F_4b2a0 D_4b2a0.
      stepn F_59228 D_59228.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_5922c | reflexivity | exact D_5922c | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_59230 D_59230 ltac:(cond_compute).
      stepret F_59420 D_59420 (0x4b2a4 : word) ltac:(bveq).
      stepLD F_4b2a4 D_4b2a4 (word_to_le_bytes 8 (Z_to_bv 64 0x90498)) (Z_to_bv 64 0x90498) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_4b2a8 D_4b2a8 ltac:(cond_compute).
      stepLD F_4b2ac D_4b2ac (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(addr_norm; rdn_by Msl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_4b2b0 D_4b2b0.
      stepn F_4b2c8 D_4b2c8.
      stepST F_4b2cc D_4b2cc (Z_to_bv 64 0x90488) (Z_to_bv 64 0) ltac:(sok_data).
      stepb_ft F_4b2d0 D_4b2d0 ltac:(cond_compute).
      stepLD F_4b2d4 D_4b2d4 (word_to_le_bytes 8 (Z_to_bv 64 0x90498)) (Z_to_bv 64 0x90498) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_4b2d8 D_4b2d8.
      stepn F_4b2dc D_4b2dc.
      stepLD F_4b2e0 D_4b2e0 (word_to_le_bytes 8 (Z_to_bv 64 0x4b408)) (Z_to_bv 64 0x4b408) ltac:(addr_norm; rdn_by Mf0) ltac:(apply bytes_le_to_Z_8).
      stepLD F_4b2e4 D_4b2e4 (word_to_le_bytes 8 (Z_to_bv 64 0x20520)) (Z_to_bv 64 0x20520) ltac:(addr_norm; rdn_by Ma0) ltac:(apply bytes_le_to_Z_8).
      stepn F_4b2e8 D_4b2e8.
      stepn F_4b2ec D_4b2ec.
      stepLD F_594b0 D_594b0 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_594b4 D_594b4 ltac:(cond_compute).
      stepret F_594b8 D_594b8 (0x4b2f0 : word) ltac:(bveq).
      stepn F_4b2f0 D_4b2f0.
      stepret F_4b2f4 D_4b2f4 (0x4b408 : word) ltac:(bveq).
      stepret F_4b408 D_4b408 (0x20520 : word) ltac:(bveq).
      stepn F_20520 D_20520.
      stepLBU F_20524 D_20524 (Z_to_bv 8 0) ltac:(addr_norm; rdn_by Mcb).
      stepb_ft F_20528 D_20528 ltac:(cond_compute).
      stepret F_2052c D_2052c (0x4b2f8 : word) ltac:(bveq).
      stepn F_4b2f8 D_4b2f8.
      stepn F_4b2fc D_4b2fc.
      stepn F_59228 D_59228.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_5922c | reflexivity | exact D_5922c | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_59230 D_59230 ltac:(cond_compute).
      stepret F_59420 D_59420 (0x4b300 : word) ltac:(bveq).
      stepLD F_4b300 D_4b300 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_4b304 D_4b304.
      stepST F_4b308 D_4b308 (Z_to_bv 64 0x90488) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
      stepb_ft F_4b30c D_4b30c ltac:(cond_compute).
      stepLD F_4b310 D_4b310 (word_to_le_bytes 8 (Z_to_bv 64 0x90498)) (Z_to_bv 64 0x90498) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_4b314 D_4b314.
      stepLD F_4b2b4 D_4b2b4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mnx) ltac:(apply bytes_le_to_Z_8).
      stepn F_4b2b8 D_4b2b8.
      stepST F_4b2bc D_4b2bc (Z_to_bv 64 0x90488) (Z_to_bv 64 32) ltac:(sok_data).
      stepST F_4b2c0 D_4b2c0 (Z_to_bv 64 0x90490) (Z_to_bv 64 0) ltac:(sok_data).
      stepb_tk F_4b2c4 D_4b2c4 ltac:(cond_compute).
      stepn F_4b318 D_4b318.
      stepST F_4b31c D_4b31c (Z_to_bv 64 0x90480) (Z_to_bv 64 1) ltac:(sok_data).
      change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
      stepn F_4b320 D_4b320.
      stepLD8 F_4b324 D_4b324 (Z_to_bv 64 0x4b4c0).
      stepLD8 F_4b328 D_4b328 code.
      stepLD8 F_4b32c D_4b32c (getr regs 9).
      stepLD8 F_4b330 D_4b330 (getr regs 18).
      stepLD8 F_4b334 D_4b334 (getr regs 19).
      stepn F_4b338 D_4b338. sp_renorm.
      stepn F_4b33c D_4b33c.
      stepLD F_594b0 D_594b0 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_594b4 D_594b4 ltac:(cond_compute).
      stepret F_594b8 D_594b8 (0x4b4c0 : word) ltac:(bveq).
      stepn F_4b4c0 D_4b4c0.
      apply mst_refl.
    - repeat split; gres; try reflexivity. exact Htp. }
Qed.

Definition mem_w2 (mem : word -> option byte) (sp code s1v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x4b4c4)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x4b440)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x5b1e8)))
    (Z_to_bv 64 0x5f8b8) [Z_to_bv 8 1].

Lemma w2 : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x4b4c4 -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x5e5f8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x5b1f0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5e600) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x5b1e8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5b1e8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x20068)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5f8b8) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x5e4c8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x4b340)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5f608) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x5f608)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5e4d0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x4b410 : word) mem rom)
                 (mkst regs' (0x4e224 : word) (mem_w2 mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x4b4c8
    /\ getr regs' 9 = s1v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hra Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mdso Mg2.
  unfold mem_w2. eexists. split.
  - 
    stepn F_4b410 D_4b410. rewrite Hsp. sp_renorm.
    stepST F_4b414 D_4b414 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x4b4c4) ltac:(sok_stack SOK).
    stepST F_4b418 D_4b418 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_4b41c D_4b41c (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    stepn F_4b420 D_4b420.
    stepn F_4b424 D_4b424.
    stepLD8 F_4b428 D_4b428 (Z_to_bv 64 0x5b1f0).
    stepLD8 F_4b42c D_4b42c (Z_to_bv 64 0x5b1e8).
    stepb_ft F_4b430 D_4b430 ltac:(cond_compute).
    stepLD8 F_4b434 D_4b434 (Z_to_bv 64 0x20068).
    stepn F_4b438 D_4b438.
    stepjr F_4b43c D_4b43c (Z_to_bv 64 0x20068) ltac:(gres; reflexivity). vnorm.
    stepn F_20068 D_20068. sp_renorm.
    stepST F_2006c D_2006c (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x4b440) ltac:(sok_stack SOK).
    stepST F_20070 D_20070 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x5b1e8) ltac:(sok_stack SOK).
    stepn F_20074 D_20074.
    stepn F_20078 D_20078.
    stepn F_2007c D_2007c.
    stepLBU F_20080 D_20080 (Z_to_bv 8 0) ltac:(rewrite v_addi_0; rdn_by Mcomp).
    stepn F_20084 D_20084.
    stepb_tk F_20088 D_20088 ltac:(cond_compute).
    stepn F_20094 D_20094.
    stepn F_20098 D_20098.
    stepn F_2009c D_2009c.
    stepST F_200a0 D_200a0 (Z_to_bv 64 0x5f8b8) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_200a4 D_200a4.
    stepLD8 F_200a8 D_200a8 (Z_to_bv 64 0x4b340).
    stepb_ft F_200ac D_200ac ltac:(cond_compute).
    stepn F_200b0 D_200b0.
    stepn F_200b4 D_200b4.
    stepn F_200b8 D_200b8.
    stepLD8 F_200bc D_200bc (Z_to_bv 64 0x5f608).
    stepn F_200c0 D_200c0.
    stepret F_4b340 D_4b340 (0x200c4 : word) ltac:(bveq).
    stepn F_200c4 D_200c4.
    stepn F_200c8 D_200c8.
    stepLD8 F_200cc D_200cc (Z_to_bv 64 0).
    stepb_tk F_200d0 D_200d0 ltac:(cond_compute).
    stepLD8 F_200e8 D_200e8 (Z_to_bv 64 0x4b440).
    stepLD8 F_200ec D_200ec (Z_to_bv 64 0x5b1e8).
    stepn F_200f0 D_200f0. sp_renorm.
    stepret F_200f4 D_200f4 (0x4b440 : word) ltac:(bveq).
    stepn F_4b440 D_4b440.
    stepb_ft F_4b444 D_4b444 ltac:(cond_compute).
    stepLD8 F_4b448 D_4b448 (Z_to_bv 64 0x4b4c4).
    stepLD8 F_4b44c D_4b44c code.
    stepLD8 F_4b450 D_4b450 s1v.
    stepn F_4b454 D_4b454. sp_renorm.
    stepn F_4b458 D_4b458.
    stepret F_4b40c D_4b40c (0x4b4c4 : word) ltac:(bveq).
    stepn F_4b4c4 D_4b4c4.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End FPX_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
