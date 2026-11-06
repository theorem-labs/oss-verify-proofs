(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic Es0ExitBase.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Es0_code_r99768_9976c Es0_code_r34324_34354 Es0_code_r56d4c_56d5c Es0_code_r1ff24_20000 Es0_code_r20000_21000 Es0_code_r4b000_4c000 Es0_code_r4d000_4e000 Es0_code_r55a7c_55a80 Es0_code_r98734_98800 Es0_code_ra9ec0_a9ecc Es0_code_r988c8_988cc Es0_code_r33a9c_33b2c Es0_code_r58000_59000.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import BMode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Inductive axv : Type := AX0 | AXg | AXgc | AXgs | AXgcs | AXgsc.
Definition atexit_cells (mem : word -> option byte) (ax : axv) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0xeb08c) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0))
  /\ match ax with
     | AX0 => rdn RSEGS mem (Z_to_bv 64 0xeb098) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
     | AXg => rdn RSEGS mem (Z_to_bv 64 0xeb098) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xeb0a0))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb090) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb0a0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb0a8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x9bda4))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb1a8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x3496c))
     | AXgc => rdn RSEGS mem (Z_to_bv 64 0xeb098) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xeb0a0))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb090) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 2))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb0a0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb0a8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x9bda4))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb1a8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x3496c))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb0b0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x583d0))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb1b0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb92f8))
     | AXgs => rdn RSEGS mem (Z_to_bv 64 0xeb098) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xeb0a0))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb090) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 3))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb0a0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb0a8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x9bda4))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb1a8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x3496c))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb0b0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x58968))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb1b0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xc9648))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb0b8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x58968))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb1b8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xc9668))
         /\ rdn RSEGS mem (Z_to_bv 64 0xc9648) 1%nat = Some [Z_to_bv 8 16]
         /\ rdn RSEGS mem (Z_to_bv 64 0xc9668) 1%nat = Some [Z_to_bv 8 6]
     | AXgcs => rdn RSEGS mem (Z_to_bv 64 0xeb098) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xeb0a0))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb090) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb0a0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb0a8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x9bda4))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb1a8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x3496c))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb0b0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x583d0))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb1b0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb92f8))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb0b8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x58968))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb1b8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xc9648))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb0c0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x58968))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb1c0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xc9668))
         /\ rdn RSEGS mem (Z_to_bv 64 0xc9648) 1%nat = Some [Z_to_bv 8 16]
         /\ rdn RSEGS mem (Z_to_bv 64 0xc9668) 1%nat = Some [Z_to_bv 8 6]
     | AXgsc => rdn RSEGS mem (Z_to_bv 64 0xeb098) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xeb0a0))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb090) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb0a0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb0a8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x9bda4))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb1a8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x3496c))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb0b0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x58968))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb1b0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xc9648))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb0b8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x58968))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb1b8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xc9668))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb0c0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x583d0))
         /\ rdn RSEGS mem (Z_to_bv 64 0xeb1c0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb92f8))
         /\ rdn RSEGS mem (Z_to_bv 64 0xc9648) 1%nat = Some [Z_to_bv 8 16]
         /\ rdn RSEGS mem (Z_to_bv 64 0xc9668) 1%nat = Some [Z_to_bv 8 6]
     end.

Lemma atexit_cells_frame : forall (M M' : word -> option byte) (ax : axv),
  (forall a : Z, ((0xeb088 <= a < 0xeb2a8) \/ (0xc9648 <= a < 0xc9649) \/ (0xc9668 <= a < 0xc9669))%Z -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> atexit_cells M ax -> atexit_cells M' ax.
Proof.
  intros M M' ax AG H.
  assert (R : forall (a : Z) (n : nat) v, (0 <= a)%Z -> (a + Z.of_nat n <= 0xeb2a8)%Z ->
             (forall x : Z, (a <= x < a + Z.of_nat n)%Z -> ((0xeb088 <= x < 0xeb2a8) \/ (0xc9648 <= x < 0xc9649) \/ (0xc9668 <= x < 0xc9669))%Z) -> rdn RSEGS M (Z_to_bv 64 a) n = v -> rdn RSEGS M' (Z_to_bv 64 a) n = v).
  { intros a n v H1 H2 HF <-. apply rdn_ext; [rewrite u_Z2bv by lia; lia|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
    rewrite <- (Z_to_bv_bv_unsigned 64 x). apply AG. apply HF. lia. }
  unfold atexit_cells in *. destruct H as (H0 & H).
  split; [apply R; [lia | cbn; lia | intros x Hx; cbn in Hx; lia | exact H0]|].
  destruct ax; repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end;
    repeat split; (apply R; [lia | cbn; lia | intros x Hx; cbn in Hx; lia | assumption]).
Qed.

Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.

Definition ax_writes (ax : axv) (m : word -> option byte) : word -> option byte :=
  match ax with
  | AX0 => m
  | AXg => wbytes (wbytes (wbytes (wbytes (m)
      (Z_to_bv 64 0xeb090) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 0xeb090) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
      (Z_to_bv 64 0xeb090) (word_to_le_bytes 4 (Z_to_bv 64 32)))
      (Z_to_bv 64 0xeb098) (word_to_le_bytes 8 (Z_to_bv 64 0))
  | AXgc => wbytes (wbytes (wbytes (wbytes (wbytes (m)
      (Z_to_bv 64 0xeb090) (word_to_le_bytes 4 (Z_to_bv 64 1)))
      (Z_to_bv 64 0xeb090) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 0xeb090) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
      (Z_to_bv 64 0xeb090) (word_to_le_bytes 4 (Z_to_bv 64 32)))
      (Z_to_bv 64 0xeb098) (word_to_le_bytes 8 (Z_to_bv 64 0))
  | AXgs => wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m)
      (Z_to_bv 64 0xeb090) (word_to_le_bytes 4 (Z_to_bv 64 2)))
      (Z_to_bv 64 0xeb090) (word_to_le_bytes 4 (Z_to_bv 64 1)))
      (Z_to_bv 64 0xeb090) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 0xeb090) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
      (Z_to_bv 64 0xeb090) (word_to_le_bytes 4 (Z_to_bv 64 32)))
      (Z_to_bv 64 0xeb098) (word_to_le_bytes 8 (Z_to_bv 64 0))
  | AXgcs => wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m)
      (Z_to_bv 64 0xeb090) (word_to_le_bytes 4 (Z_to_bv 64 3)))
      (Z_to_bv 64 0xeb090) (word_to_le_bytes 4 (Z_to_bv 64 2)))
      (Z_to_bv 64 0xeb090) (word_to_le_bytes 4 (Z_to_bv 64 1)))
      (Z_to_bv 64 0xeb090) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 0xeb090) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
      (Z_to_bv 64 0xeb090) (word_to_le_bytes 4 (Z_to_bv 64 32)))
      (Z_to_bv 64 0xeb098) (word_to_le_bytes 8 (Z_to_bv 64 0))
  | AXgsc => wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m)
      (Z_to_bv 64 0xeb090) (word_to_le_bytes 4 (Z_to_bv 64 3)))
      (Z_to_bv 64 0xeb090) (word_to_le_bytes 4 (Z_to_bv 64 2)))
      (Z_to_bv 64 0xeb090) (word_to_le_bytes 4 (Z_to_bv 64 1)))
      (Z_to_bv 64 0xeb090) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 0xeb090) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
      (Z_to_bv 64 0xeb090) (word_to_le_bytes 4 (Z_to_bv 64 32)))
      (Z_to_bv 64 0xeb098) (word_to_le_bytes 8 (Z_to_bv 64 0))
  end.
Definition mem_w1 (ax : axv) (mem : word -> option byte) (sp ra s0 : word) (tid : Z) (code s1 s2 s3 : word) :=
  wbytes (ax_writes ax (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (bv_unsigned sp - 16)) (word_to_le_bytes 8 s0))
    (Z_to_bv 64 0xeb2a8) (word_to_le_bytes 4 (Z_to_bv 64 tid)))

    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x9be5c)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3)))
    (Z_to_bv 64 0xeb088) [Z_to_bv 8 1].

Lemma w1 : forall (ax : axv) regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn RSEGS mem (Z_to_bv 64 0xeb2a8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  stdio_globals mem ->
  rdn RSEGS mem (Z_to_bv 64 0xc9614) 1%nat = Some [Z_to_bv 8 0] ->
  atexit_cells mem ax ->
  exists regs',
    msteps RSEGS (mkst regs (0x9bdf8 : word) mem rom)
                 (mkst regs' (0x9bdac : word) (mem_w1 ax mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x9be60
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros ax regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock GL Mcb AX.
  destruct GL as (Gnl & _).
  destruct ax.
  {
    destruct AX as (Mxl & Mxh). unfold mem_w1, ax_writes. eexists. split.
    -
      stepn F_9bdac D_9bdac. rewrite Hsp. sp_renorm.

      stepST F_9bdb0 D_9bdb0 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
      stepST F_9bdb4 D_9bdb4 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).

      stepn F_9bdb8 D_9bdb8.
      stepn F_9bdbc D_9bdbc. rewrite Htp.

      stepLD F_9bdc0 D_9bdc0 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
        ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      rewrite (v_lw_small tid) by lia.

      stepn F_9bdc4 D_9bdc4.
      stepn F_9bdc8 D_9bdc8.

      eapply mst_step; [reflexivity
        | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
          [ exact F_9bdcc | reflexivity | exact D_9bdcc
          | gres; u_norm; reflexivity
          | gres; rdn_by Mlock
          | apply bytes_le_to_Z_4; u_norm; lia ]
        | ].
      reduce_bv_eqb_ifs; norm_pc_r; vnorm.

      eapply mst_step; [reflexivity
        | eapply step_bne_ft_r; [exact F_9bdd0 | reflexivity | exact D_9bdd0 | gres; cond_compute ] | ].
      norm_pc_r.

      eapply mst_step; [reflexivity
        | eapply step_sc_w_ok; [exact F_9bdd4 | reflexivity | exact D_9bdd4
          | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
      step_simpl; vnorm.

      stepb_ft F_9bdd8 D_9bdd8 ltac:(cond_compute).

      stepn F_9bddc D_9bddc.

      stepb_ft F_9bde0 D_9bde0 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).

      stepb_tk F_9bde4 D_9bde4 ltac:(cond_compute).

      stepn F_9be08 D_9be08. rewrite Ha0.

      stepn F_9be0c D_9be0c.

      stepn F_9bb00 D_9bb00. sp_renorm.
      stepST F_9bb04 D_9bb04 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x9be5c) ltac:(sok_stack SOK).
      stepST F_9bb08 D_9bb08 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
      stepST F_9bb0c D_9bb0c (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
      stepST F_9bb10 D_9bb10 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
      stepST F_9bb14 D_9bb14 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
      stepn F_9bb18 D_9bb18. stepn F_9bb1c D_9bb1c. stepn F_9bb20 D_9bb20. stepn F_9bb24 D_9bb24.

      stepn F_9bb28 D_9bb28.
      stepn F_ad0d0 D_ad0d0.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_ad0d4 | reflexivity | exact D_ad0d4 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_ad0d8 D_ad0d8 ltac:(cond_compute).
      stepret F_ad2c8 D_ad2c8 (0x9bb78 : word) ltac:(bveq).

      stepLD F_9bb2c D_9bb2c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_9bb30 D_9bb30 ltac:(cond_compute).
      stepn F_9bba0 D_9bba0.
      stepST F_9bba4 D_9bba4 (Z_to_bv 64 0xeb088) (Z_to_bv 64 1) ltac:(sok_data).
      change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
      stepn F_9bba8 D_9bba8.
      stepLD8 F_9bbac D_9bbac (Z_to_bv 64 0x9be5c).
      stepLD8 F_9bbb0 D_9bbb0 code.
      stepLD8 F_9bbb4 D_9bbb4 (getr regs 9).
      stepLD8 F_9bbb8 D_9bbb8 (getr regs 18).
      stepLD8 F_9bbbc D_9bbbc (getr regs 19).
      stepn F_9bbc0 D_9bbc0. sp_renorm.

      stepn F_9bbc4 D_9bbc4.
      stepLD F_ad358 D_ad358 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_ad35c D_ad35c ltac:(cond_compute).
      stepret F_ad360 D_ad360 (0x9be5c : word) ltac:(bveq).
      stepn F_9be10 D_9be10.
      apply mst_refl.
    - repeat split; gres; try reflexivity. exact Htp. }
  {
    destruct AX as (Mxl & Mxh & Msl & Mnx & Mf0 & Ma0). unfold mem_w1, ax_writes. eexists. split.
    -
      stepn F_9bdac D_9bdac. rewrite Hsp. sp_renorm.

      stepST F_9bdb0 D_9bdb0 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
      stepST F_9bdb4 D_9bdb4 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).

      stepn F_9bdb8 D_9bdb8.
      stepn F_9bdbc D_9bdbc. rewrite Htp.

      stepLD F_9bdc0 D_9bdc0 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
        ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      rewrite (v_lw_small tid) by lia.

      stepn F_9bdc4 D_9bdc4.
      stepn F_9bdc8 D_9bdc8.

      eapply mst_step; [reflexivity
        | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
          [ exact F_9bdcc | reflexivity | exact D_9bdcc
          | gres; u_norm; reflexivity
          | gres; rdn_by Mlock
          | apply bytes_le_to_Z_4; u_norm; lia ]
        | ].
      reduce_bv_eqb_ifs; norm_pc_r; vnorm.

      eapply mst_step; [reflexivity
        | eapply step_bne_ft_r; [exact F_9bdd0 | reflexivity | exact D_9bdd0 | gres; cond_compute ] | ].
      norm_pc_r.

      eapply mst_step; [reflexivity
        | eapply step_sc_w_ok; [exact F_9bdd4 | reflexivity | exact D_9bdd4
          | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
      step_simpl; vnorm.

      stepb_ft F_9bdd8 D_9bdd8 ltac:(cond_compute).

      stepn F_9bddc D_9bddc.

      stepb_ft F_9bde0 D_9bde0 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).

      stepb_tk F_9bde4 D_9bde4 ltac:(cond_compute).

      stepn F_9be08 D_9be08. rewrite Ha0.

      stepn F_9be0c D_9be0c.

      stepn F_9bb00 D_9bb00. sp_renorm.
      stepST F_9bb04 D_9bb04 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x9be5c) ltac:(sok_stack SOK).
      stepST F_9bb08 D_9bb08 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
      stepST F_9bb0c D_9bb0c (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
      stepST F_9bb10 D_9bb10 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
      stepST F_9bb14 D_9bb14 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
      stepn F_9bb18 D_9bb18. stepn F_9bb1c D_9bb1c. stepn F_9bb20 D_9bb20. stepn F_9bb24 D_9bb24.

      stepn F_9bb28 D_9bb28.
      stepn F_ad0d0 D_ad0d0.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_ad0d4 | reflexivity | exact D_ad0d4 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_ad0d8 D_ad0d8 ltac:(cond_compute).
      stepret F_ad2c8 D_ad2c8 (0x9bb78 : word) ltac:(bveq).

      stepLD F_9bb2c D_9bb2c (word_to_le_bytes 8 (Z_to_bv 64 0xeb0a0)) (Z_to_bv 64 0xeb0a0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_9bb30 D_9bb30 ltac:(cond_compute).
      stepLD F_9bb34 D_9bb34 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(addr_norm; rdn_by Msl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9bb38 D_9bb38.
      stepn F_9bb50 D_9bb50.

      stepST F_9bb54 D_9bb54 (Z_to_bv 64 0xeb090) (Z_to_bv 64 0) ltac:(sok_data).
      stepb_ft F_9bb58 D_9bb58 ltac:(cond_compute).

      stepLD F_9bb5c D_9bb5c (word_to_le_bytes 8 (Z_to_bv 64 0xeb0a0)) (Z_to_bv 64 0xeb0a0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_9bb60 D_9bb60.
      stepn F_9bb64 D_9bb64.
      stepLD F_9bb68 D_9bb68 (word_to_le_bytes 8 (Z_to_bv 64 0x9bda4)) (Z_to_bv 64 0x9bda4) ltac:(addr_norm; rdn_by Mf0) ltac:(apply bytes_le_to_Z_8).
      stepLD F_9bb6c D_9bb6c (word_to_le_bytes 8 (Z_to_bv 64 0x3496c)) (Z_to_bv 64 0x3496c) ltac:(addr_norm; rdn_by Ma0) ltac:(apply bytes_le_to_Z_8).

      stepn F_9bb70 D_9bb70.
      stepn F_9bb74 D_9bb74.
      stepLD F_ad358 D_ad358 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_ad35c D_ad35c ltac:(cond_compute).
      stepret F_ad360 D_ad360 (0x9bbc4 : word) ltac:(bveq).
      stepn F_9bb78 D_9bb78.
      stepret F_9bb7c D_9bb7c (0x9bda4 : word) ltac:(bveq).

      stepret F_9bd58 D_9bd58 (0x3496c : word) ltac:(bveq).
      stepn F_34914 D_34914.
      stepLBU F_34918 D_34918 (Z_to_bv 8 0) ltac:(addr_norm; rdn_by Mcb).
      stepb_ft F_3491c D_3491c ltac:(cond_compute).
      stepret F_34920 D_34920 (0x9bbcc : word) ltac:(bveq).

      stepn F_9bb80 D_9bb80.
      stepn F_9bb84 D_9bb84.
      stepn F_ad0d0 D_ad0d0.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_ad0d4 | reflexivity | exact D_ad0d4 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_ad0d8 D_ad0d8 ltac:(cond_compute).
      stepret F_ad2c8 D_ad2c8 (0x9bbd4 : word) ltac:(bveq).

      stepLD F_9bb88 D_9bb88 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9bb8c D_9bb8c.
      stepST F_9bb90 D_9bb90 (Z_to_bv 64 0xeb090) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
      stepb_ft F_9bb94 D_9bb94 ltac:(cond_compute).

      stepLD F_9bb98 D_9bb98 (word_to_le_bytes 8 (Z_to_bv 64 0xeb0a0)) (Z_to_bv 64 0xeb0a0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_9bb9c D_9bb9c.
      stepLD F_9bb3c D_9bb3c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mnx) ltac:(apply bytes_le_to_Z_8).
      stepn F_9bb40 D_9bb40.
      stepST F_9bb44 D_9bb44 (Z_to_bv 64 0xeb090) (Z_to_bv 64 32) ltac:(sok_data).
      stepST F_9bb48 D_9bb48 (Z_to_bv 64 0xeb098) (Z_to_bv 64 0) ltac:(sok_data).
      stepb_tk F_9bb4c D_9bb4c ltac:(cond_compute).
      stepn F_9bba0 D_9bba0.
      stepST F_9bba4 D_9bba4 (Z_to_bv 64 0xeb088) (Z_to_bv 64 1) ltac:(sok_data).
      change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
      stepn F_9bba8 D_9bba8.
      stepLD8 F_9bbac D_9bbac (Z_to_bv 64 0x9be5c).
      stepLD8 F_9bbb0 D_9bbb0 code.
      stepLD8 F_9bbb4 D_9bbb4 (getr regs 9).
      stepLD8 F_9bbb8 D_9bbb8 (getr regs 18).
      stepLD8 F_9bbbc D_9bbbc (getr regs 19).
      stepn F_9bbc0 D_9bbc0. sp_renorm.

      stepn F_9bbc4 D_9bbc4.
      stepLD F_ad358 D_ad358 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_ad35c D_ad35c ltac:(cond_compute).
      stepret F_ad360 D_ad360 (0x9be5c : word) ltac:(bveq).
      stepn F_9be10 D_9be10.
      apply mst_refl.
    - repeat split; gres; try reflexivity. exact Htp. }
  {
    destruct AX as (Mxl & Mxh & Msl & Mnx & Mf0 & Ma0 & Mf1 & Ma1). unfold mem_w1, ax_writes. eexists. split.
    -
      stepn F_9bdac D_9bdac. rewrite Hsp. sp_renorm.

      stepST F_9bdb0 D_9bdb0 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
      stepST F_9bdb4 D_9bdb4 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).

      stepn F_9bdb8 D_9bdb8.
      stepn F_9bdbc D_9bdbc. rewrite Htp.

      stepLD F_9bdc0 D_9bdc0 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
        ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      rewrite (v_lw_small tid) by lia.

      stepn F_9bdc4 D_9bdc4.
      stepn F_9bdc8 D_9bdc8.

      eapply mst_step; [reflexivity
        | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
          [ exact F_9bdcc | reflexivity | exact D_9bdcc
          | gres; u_norm; reflexivity
          | gres; rdn_by Mlock
          | apply bytes_le_to_Z_4; u_norm; lia ]
        | ].
      reduce_bv_eqb_ifs; norm_pc_r; vnorm.

      eapply mst_step; [reflexivity
        | eapply step_bne_ft_r; [exact F_9bdd0 | reflexivity | exact D_9bdd0 | gres; cond_compute ] | ].
      norm_pc_r.

      eapply mst_step; [reflexivity
        | eapply step_sc_w_ok; [exact F_9bdd4 | reflexivity | exact D_9bdd4
          | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
      step_simpl; vnorm.

      stepb_ft F_9bdd8 D_9bdd8 ltac:(cond_compute).

      stepn F_9bddc D_9bddc.

      stepb_ft F_9bde0 D_9bde0 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).

      stepb_tk F_9bde4 D_9bde4 ltac:(cond_compute).

      stepn F_9be08 D_9be08. rewrite Ha0.

      stepn F_9be0c D_9be0c.

      stepn F_9bb00 D_9bb00. sp_renorm.
      stepST F_9bb04 D_9bb04 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x9be5c) ltac:(sok_stack SOK).
      stepST F_9bb08 D_9bb08 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
      stepST F_9bb0c D_9bb0c (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
      stepST F_9bb10 D_9bb10 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
      stepST F_9bb14 D_9bb14 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
      stepn F_9bb18 D_9bb18. stepn F_9bb1c D_9bb1c. stepn F_9bb20 D_9bb20. stepn F_9bb24 D_9bb24.

      stepn F_9bb28 D_9bb28.
      stepn F_ad0d0 D_ad0d0.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_ad0d4 | reflexivity | exact D_ad0d4 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_ad0d8 D_ad0d8 ltac:(cond_compute).
      stepret F_ad2c8 D_ad2c8 (0x9bb78 : word) ltac:(bveq).

      stepLD F_9bb2c D_9bb2c (word_to_le_bytes 8 (Z_to_bv 64 0xeb0a0)) (Z_to_bv 64 0xeb0a0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_9bb30 D_9bb30 ltac:(cond_compute).
      stepLD F_9bb34 D_9bb34 (word_to_le_bytes 4 (Z_to_bv 64 2)) (Z_to_bv 64 2) ltac:(addr_norm; rdn_by Msl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9bb38 D_9bb38.
      stepn F_9bb50 D_9bb50.

      stepST F_9bb54 D_9bb54 (Z_to_bv 64 0xeb090) (Z_to_bv 64 1) ltac:(sok_data).
      stepb_ft F_9bb58 D_9bb58 ltac:(cond_compute).

      stepLD F_9bb5c D_9bb5c (word_to_le_bytes 8 (Z_to_bv 64 0xeb0a0)) (Z_to_bv 64 0xeb0a0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_9bb60 D_9bb60.
      stepn F_9bb64 D_9bb64.
      stepLD F_9bb68 D_9bb68 (word_to_le_bytes 8 (Z_to_bv 64 0x583d0)) (Z_to_bv 64 0x583d0) ltac:(addr_norm; rdn_by Mf1) ltac:(apply bytes_le_to_Z_8).
      stepLD F_9bb6c D_9bb6c (word_to_le_bytes 8 (Z_to_bv 64 0xb92f8)) (Z_to_bv 64 0xb92f8) ltac:(addr_norm; rdn_by Ma1) ltac:(apply bytes_le_to_Z_8).

      stepn F_9bb70 D_9bb70.
      stepn F_9bb74 D_9bb74.
      stepLD F_ad358 D_ad358 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_ad35c D_ad35c ltac:(cond_compute).
      stepret F_ad360 D_ad360 (0x9bbc4 : word) ltac:(bveq).
      stepn F_9bb78 D_9bb78.
      stepret F_9bb7c D_9bb7c (0x583d0 : word) ltac:(bveq).
      stepret F_58378 D_58378 (0x9bbcc : word) ltac:(bveq).

      stepn F_9bb80 D_9bb80.
      stepn F_9bb84 D_9bb84.
      stepn F_ad0d0 D_ad0d0.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_ad0d4 | reflexivity | exact D_ad0d4 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_ad0d8 D_ad0d8 ltac:(cond_compute).
      stepret F_ad2c8 D_ad2c8 (0x9bbd4 : word) ltac:(bveq).

      stepLD F_9bb88 D_9bb88 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1)
        ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9bb8c D_9bb8c.
      stepST F_9bb90 D_9bb90 (Z_to_bv 64 0xeb090) (Z_to_bv 64 0) ltac:(sok_data).
      stepb_tk F_9bb94 D_9bb94 ltac:(cond_compute).

      stepLD F_9bb5c D_9bb5c (word_to_le_bytes 8 (Z_to_bv 64 0xeb0a0)) (Z_to_bv 64 0xeb0a0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_9bb60 D_9bb60.
      stepn F_9bb64 D_9bb64.
      stepLD F_9bb68 D_9bb68 (word_to_le_bytes 8 (Z_to_bv 64 0x9bda4)) (Z_to_bv 64 0x9bda4) ltac:(addr_norm; rdn_by Mf0) ltac:(apply bytes_le_to_Z_8).
      stepLD F_9bb6c D_9bb6c (word_to_le_bytes 8 (Z_to_bv 64 0x3496c)) (Z_to_bv 64 0x3496c) ltac:(addr_norm; rdn_by Ma0) ltac:(apply bytes_le_to_Z_8).

      stepn F_9bb70 D_9bb70.
      stepn F_9bb74 D_9bb74.
      stepLD F_ad358 D_ad358 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_ad35c D_ad35c ltac:(cond_compute).
      stepret F_ad360 D_ad360 (0x9bbc4 : word) ltac:(bveq).
      stepn F_9bb78 D_9bb78.
      stepret F_9bb7c D_9bb7c (0x9bda4 : word) ltac:(bveq).

      stepret F_9bd58 D_9bd58 (0x3496c : word) ltac:(bveq).
      stepn F_34914 D_34914.
      stepLBU F_34918 D_34918 (Z_to_bv 8 0) ltac:(addr_norm; rdn_by Mcb).
      stepb_ft F_3491c D_3491c ltac:(cond_compute).
      stepret F_34920 D_34920 (0x9bbcc : word) ltac:(bveq).

      stepn F_9bb80 D_9bb80.
      stepn F_9bb84 D_9bb84.
      stepn F_ad0d0 D_ad0d0.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_ad0d4 | reflexivity | exact D_ad0d4 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_ad0d8 D_ad0d8 ltac:(cond_compute).
      stepret F_ad2c8 D_ad2c8 (0x9bbd4 : word) ltac:(bveq).

      stepLD F_9bb88 D_9bb88 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9bb8c D_9bb8c.
      stepST F_9bb90 D_9bb90 (Z_to_bv 64 0xeb090) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
      stepb_ft F_9bb94 D_9bb94 ltac:(cond_compute).

      stepLD F_9bb98 D_9bb98 (word_to_le_bytes 8 (Z_to_bv 64 0xeb0a0)) (Z_to_bv 64 0xeb0a0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_9bb9c D_9bb9c.
      stepLD F_9bb3c D_9bb3c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mnx) ltac:(apply bytes_le_to_Z_8).
      stepn F_9bb40 D_9bb40.
      stepST F_9bb44 D_9bb44 (Z_to_bv 64 0xeb090) (Z_to_bv 64 32) ltac:(sok_data).
      stepST F_9bb48 D_9bb48 (Z_to_bv 64 0xeb098) (Z_to_bv 64 0) ltac:(sok_data).
      stepb_tk F_9bb4c D_9bb4c ltac:(cond_compute).
      stepn F_9bba0 D_9bba0.
      stepST F_9bba4 D_9bba4 (Z_to_bv 64 0xeb088) (Z_to_bv 64 1) ltac:(sok_data).
      change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
      stepn F_9bba8 D_9bba8.
      stepLD8 F_9bbac D_9bbac (Z_to_bv 64 0x9be5c).
      stepLD8 F_9bbb0 D_9bbb0 code.
      stepLD8 F_9bbb4 D_9bbb4 (getr regs 9).
      stepLD8 F_9bbb8 D_9bbb8 (getr regs 18).
      stepLD8 F_9bbbc D_9bbbc (getr regs 19).
      stepn F_9bbc0 D_9bbc0. sp_renorm.

      stepn F_9bbc4 D_9bbc4.
      stepLD F_ad358 D_ad358 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_ad35c D_ad35c ltac:(cond_compute).
      stepret F_ad360 D_ad360 (0x9be5c : word) ltac:(bveq).
      stepn F_9be10 D_9be10.
      apply mst_refl.
    - repeat split; gres; try reflexivity. exact Htp. }
  {
    destruct AX as (Mxl & Mxh & Msl & Mnx & Mf0 & Ma0 & Mf1 & Ma1 & Mf2 & Ma2 & Msinf & Msnan). unfold mem_w1, ax_writes. eexists. split.
    -
      stepn F_9bdac D_9bdac. rewrite Hsp. sp_renorm.

      stepST F_9bdb0 D_9bdb0 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
      stepST F_9bdb4 D_9bdb4 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).

      stepn F_9bdb8 D_9bdb8.
      stepn F_9bdbc D_9bdbc. rewrite Htp.

      stepLD F_9bdc0 D_9bdc0 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
        ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      rewrite (v_lw_small tid) by lia.

      stepn F_9bdc4 D_9bdc4.
      stepn F_9bdc8 D_9bdc8.

      eapply mst_step; [reflexivity
        | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
          [ exact F_9bdcc | reflexivity | exact D_9bdcc
          | gres; u_norm; reflexivity
          | gres; rdn_by Mlock
          | apply bytes_le_to_Z_4; u_norm; lia ]
        | ].
      reduce_bv_eqb_ifs; norm_pc_r; vnorm.

      eapply mst_step; [reflexivity
        | eapply step_bne_ft_r; [exact F_9bdd0 | reflexivity | exact D_9bdd0 | gres; cond_compute ] | ].
      norm_pc_r.

      eapply mst_step; [reflexivity
        | eapply step_sc_w_ok; [exact F_9bdd4 | reflexivity | exact D_9bdd4
          | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
      step_simpl; vnorm.

      stepb_ft F_9bdd8 D_9bdd8 ltac:(cond_compute).

      stepn F_9bddc D_9bddc.

      stepb_ft F_9bde0 D_9bde0 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).

      stepb_tk F_9bde4 D_9bde4 ltac:(cond_compute).

      stepn F_9be08 D_9be08. rewrite Ha0.

      stepn F_9be0c D_9be0c.

      stepn F_9bb00 D_9bb00. sp_renorm.
      stepST F_9bb04 D_9bb04 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x9be5c) ltac:(sok_stack SOK).
      stepST F_9bb08 D_9bb08 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
      stepST F_9bb0c D_9bb0c (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
      stepST F_9bb10 D_9bb10 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
      stepST F_9bb14 D_9bb14 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
      stepn F_9bb18 D_9bb18. stepn F_9bb1c D_9bb1c. stepn F_9bb20 D_9bb20. stepn F_9bb24 D_9bb24.

      stepn F_9bb28 D_9bb28.
      stepn F_ad0d0 D_ad0d0.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_ad0d4 | reflexivity | exact D_ad0d4 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_ad0d8 D_ad0d8 ltac:(cond_compute).
      stepret F_ad2c8 D_ad2c8 (0x9bb78 : word) ltac:(bveq).

      stepLD F_9bb2c D_9bb2c (word_to_le_bytes 8 (Z_to_bv 64 0xeb0a0)) (Z_to_bv 64 0xeb0a0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_9bb30 D_9bb30 ltac:(cond_compute).
      stepLD F_9bb34 D_9bb34 (word_to_le_bytes 4 (Z_to_bv 64 3)) (Z_to_bv 64 3) ltac:(addr_norm; rdn_by Msl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9bb38 D_9bb38.
      stepn F_9bb50 D_9bb50.

      stepST F_9bb54 D_9bb54 (Z_to_bv 64 0xeb090) (Z_to_bv 64 2) ltac:(sok_data).
      stepb_ft F_9bb58 D_9bb58 ltac:(cond_compute).

      stepLD F_9bb5c D_9bb5c (word_to_le_bytes 8 (Z_to_bv 64 0xeb0a0)) (Z_to_bv 64 0xeb0a0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_9bb60 D_9bb60.
      stepn F_9bb64 D_9bb64.
      stepLD F_9bb68 D_9bb68 (word_to_le_bytes 8 (Z_to_bv 64 0x58968)) (Z_to_bv 64 0x58968) ltac:(addr_norm; rdn_by Mf2) ltac:(apply bytes_le_to_Z_8).
      stepLD F_9bb6c D_9bb6c (word_to_le_bytes 8 (Z_to_bv 64 0xc9668)) (Z_to_bv 64 0xc9668) ltac:(addr_norm; rdn_by Ma2) ltac:(apply bytes_le_to_Z_8).

      stepn F_9bb70 D_9bb70.
      stepn F_9bb74 D_9bb74.
      stepLD F_ad358 D_ad358 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_ad35c D_ad35c ltac:(cond_compute).
      stepret F_ad360 D_ad360 (0x9bbc4 : word) ltac:(bveq).
      stepn F_9bb78 D_9bb78.
      stepret F_9bb7c D_9bb7c (0x58968 : word) ltac:(bveq).

      stepLBU F_58910 D_58910 (Z_to_bv 8 6) ltac:(addr_norm; rdn_by Msnan).
      stepn F_58914 D_58914.
      stepb_ft F_58918 D_58918 ltac:(cond_compute).
      stepret F_5891c D_5891c (0x9bbcc : word) ltac:(bveq).

      stepn F_9bb80 D_9bb80.
      stepn F_9bb84 D_9bb84.
      stepn F_ad0d0 D_ad0d0.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_ad0d4 | reflexivity | exact D_ad0d4 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_ad0d8 D_ad0d8 ltac:(cond_compute).
      stepret F_ad2c8 D_ad2c8 (0x9bbd4 : word) ltac:(bveq).

      stepLD F_9bb88 D_9bb88 (word_to_le_bytes 4 (Z_to_bv 64 2)) (Z_to_bv 64 2)
        ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9bb8c D_9bb8c.
      stepST F_9bb90 D_9bb90 (Z_to_bv 64 0xeb090) (Z_to_bv 64 1) ltac:(sok_data).
      stepb_tk F_9bb94 D_9bb94 ltac:(cond_compute).

      stepLD F_9bb5c D_9bb5c (word_to_le_bytes 8 (Z_to_bv 64 0xeb0a0)) (Z_to_bv 64 0xeb0a0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_9bb60 D_9bb60.
      stepn F_9bb64 D_9bb64.
      stepLD F_9bb68 D_9bb68 (word_to_le_bytes 8 (Z_to_bv 64 0x58968)) (Z_to_bv 64 0x58968) ltac:(addr_norm; rdn_by Mf1) ltac:(apply bytes_le_to_Z_8).
      stepLD F_9bb6c D_9bb6c (word_to_le_bytes 8 (Z_to_bv 64 0xc9648)) (Z_to_bv 64 0xc9648) ltac:(addr_norm; rdn_by Ma1) ltac:(apply bytes_le_to_Z_8).

      stepn F_9bb70 D_9bb70.
      stepn F_9bb74 D_9bb74.
      stepLD F_ad358 D_ad358 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_ad35c D_ad35c ltac:(cond_compute).
      stepret F_ad360 D_ad360 (0x9bbc4 : word) ltac:(bveq).
      stepn F_9bb78 D_9bb78.
      stepret F_9bb7c D_9bb7c (0x58968 : word) ltac:(bveq).

      stepLBU F_58910 D_58910 (Z_to_bv 8 16) ltac:(addr_norm; rdn_by Msinf).
      stepn F_58914 D_58914.
      stepb_ft F_58918 D_58918 ltac:(cond_compute).
      stepret F_5891c D_5891c (0x9bbcc : word) ltac:(bveq).

      stepn F_9bb80 D_9bb80.
      stepn F_9bb84 D_9bb84.
      stepn F_ad0d0 D_ad0d0.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_ad0d4 | reflexivity | exact D_ad0d4 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_ad0d8 D_ad0d8 ltac:(cond_compute).
      stepret F_ad2c8 D_ad2c8 (0x9bbd4 : word) ltac:(bveq).

      stepLD F_9bb88 D_9bb88 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1)
        ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9bb8c D_9bb8c.
      stepST F_9bb90 D_9bb90 (Z_to_bv 64 0xeb090) (Z_to_bv 64 0) ltac:(sok_data).
      stepb_tk F_9bb94 D_9bb94 ltac:(cond_compute).

      stepLD F_9bb5c D_9bb5c (word_to_le_bytes 8 (Z_to_bv 64 0xeb0a0)) (Z_to_bv 64 0xeb0a0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_9bb60 D_9bb60.
      stepn F_9bb64 D_9bb64.
      stepLD F_9bb68 D_9bb68 (word_to_le_bytes 8 (Z_to_bv 64 0x9bda4)) (Z_to_bv 64 0x9bda4) ltac:(addr_norm; rdn_by Mf0) ltac:(apply bytes_le_to_Z_8).
      stepLD F_9bb6c D_9bb6c (word_to_le_bytes 8 (Z_to_bv 64 0x3496c)) (Z_to_bv 64 0x3496c) ltac:(addr_norm; rdn_by Ma0) ltac:(apply bytes_le_to_Z_8).

      stepn F_9bb70 D_9bb70.
      stepn F_9bb74 D_9bb74.
      stepLD F_ad358 D_ad358 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_ad35c D_ad35c ltac:(cond_compute).
      stepret F_ad360 D_ad360 (0x9bbc4 : word) ltac:(bveq).
      stepn F_9bb78 D_9bb78.
      stepret F_9bb7c D_9bb7c (0x9bda4 : word) ltac:(bveq).

      stepret F_9bd58 D_9bd58 (0x3496c : word) ltac:(bveq).
      stepn F_34914 D_34914.
      stepLBU F_34918 D_34918 (Z_to_bv 8 0) ltac:(addr_norm; rdn_by Mcb).
      stepb_ft F_3491c D_3491c ltac:(cond_compute).
      stepret F_34920 D_34920 (0x9bbcc : word) ltac:(bveq).

      stepn F_9bb80 D_9bb80.
      stepn F_9bb84 D_9bb84.
      stepn F_ad0d0 D_ad0d0.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_ad0d4 | reflexivity | exact D_ad0d4 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_ad0d8 D_ad0d8 ltac:(cond_compute).
      stepret F_ad2c8 D_ad2c8 (0x9bbd4 : word) ltac:(bveq).

      stepLD F_9bb88 D_9bb88 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9bb8c D_9bb8c.
      stepST F_9bb90 D_9bb90 (Z_to_bv 64 0xeb090) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
      stepb_ft F_9bb94 D_9bb94 ltac:(cond_compute).

      stepLD F_9bb98 D_9bb98 (word_to_le_bytes 8 (Z_to_bv 64 0xeb0a0)) (Z_to_bv 64 0xeb0a0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_9bb9c D_9bb9c.
      stepLD F_9bb3c D_9bb3c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mnx) ltac:(apply bytes_le_to_Z_8).
      stepn F_9bb40 D_9bb40.
      stepST F_9bb44 D_9bb44 (Z_to_bv 64 0xeb090) (Z_to_bv 64 32) ltac:(sok_data).
      stepST F_9bb48 D_9bb48 (Z_to_bv 64 0xeb098) (Z_to_bv 64 0) ltac:(sok_data).
      stepb_tk F_9bb4c D_9bb4c ltac:(cond_compute).
      stepn F_9bba0 D_9bba0.
      stepST F_9bba4 D_9bba4 (Z_to_bv 64 0xeb088) (Z_to_bv 64 1) ltac:(sok_data).
      change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
      stepn F_9bba8 D_9bba8.
      stepLD8 F_9bbac D_9bbac (Z_to_bv 64 0x9be5c).
      stepLD8 F_9bbb0 D_9bbb0 code.
      stepLD8 F_9bbb4 D_9bbb4 (getr regs 9).
      stepLD8 F_9bbb8 D_9bbb8 (getr regs 18).
      stepLD8 F_9bbbc D_9bbbc (getr regs 19).
      stepn F_9bbc0 D_9bbc0. sp_renorm.

      stepn F_9bbc4 D_9bbc4.
      stepLD F_ad358 D_ad358 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_ad35c D_ad35c ltac:(cond_compute).
      stepret F_ad360 D_ad360 (0x9be5c : word) ltac:(bveq).
      stepn F_9be10 D_9be10.
      apply mst_refl.
    - repeat split; gres; try reflexivity. exact Htp. }
  {
    destruct AX as (Mxl & Mxh & Msl & Mnx & Mf0 & Ma0 & Mf1 & Ma1 & Mf2 & Ma2 & Mf3 & Ma3 & Msinf & Msnan). unfold mem_w1, ax_writes. eexists. split.
    -
      stepn F_9bdac D_9bdac. rewrite Hsp. sp_renorm.

      stepST F_9bdb0 D_9bdb0 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
      stepST F_9bdb4 D_9bdb4 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).

      stepn F_9bdb8 D_9bdb8.
      stepn F_9bdbc D_9bdbc. rewrite Htp.

      stepLD F_9bdc0 D_9bdc0 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
        ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      rewrite (v_lw_small tid) by lia.

      stepn F_9bdc4 D_9bdc4.
      stepn F_9bdc8 D_9bdc8.

      eapply mst_step; [reflexivity
        | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
          [ exact F_9bdcc | reflexivity | exact D_9bdcc
          | gres; u_norm; reflexivity
          | gres; rdn_by Mlock
          | apply bytes_le_to_Z_4; u_norm; lia ]
        | ].
      reduce_bv_eqb_ifs; norm_pc_r; vnorm.

      eapply mst_step; [reflexivity
        | eapply step_bne_ft_r; [exact F_9bdd0 | reflexivity | exact D_9bdd0 | gres; cond_compute ] | ].
      norm_pc_r.

      eapply mst_step; [reflexivity
        | eapply step_sc_w_ok; [exact F_9bdd4 | reflexivity | exact D_9bdd4
          | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
      step_simpl; vnorm.

      stepb_ft F_9bdd8 D_9bdd8 ltac:(cond_compute).

      stepn F_9bddc D_9bddc.

      stepb_ft F_9bde0 D_9bde0 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).

      stepb_tk F_9bde4 D_9bde4 ltac:(cond_compute).

      stepn F_9be08 D_9be08. rewrite Ha0.

      stepn F_9be0c D_9be0c.

      stepn F_9bb00 D_9bb00. sp_renorm.
      stepST F_9bb04 D_9bb04 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x9be5c) ltac:(sok_stack SOK).
      stepST F_9bb08 D_9bb08 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
      stepST F_9bb0c D_9bb0c (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
      stepST F_9bb10 D_9bb10 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
      stepST F_9bb14 D_9bb14 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
      stepn F_9bb18 D_9bb18. stepn F_9bb1c D_9bb1c. stepn F_9bb20 D_9bb20. stepn F_9bb24 D_9bb24.

      stepn F_9bb28 D_9bb28.
      stepn F_ad0d0 D_ad0d0.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_ad0d4 | reflexivity | exact D_ad0d4 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_ad0d8 D_ad0d8 ltac:(cond_compute).
      stepret F_ad2c8 D_ad2c8 (0x9bb78 : word) ltac:(bveq).

      stepLD F_9bb2c D_9bb2c (word_to_le_bytes 8 (Z_to_bv 64 0xeb0a0)) (Z_to_bv 64 0xeb0a0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_9bb30 D_9bb30 ltac:(cond_compute).
      stepLD F_9bb34 D_9bb34 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(addr_norm; rdn_by Msl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9bb38 D_9bb38.
      stepn F_9bb50 D_9bb50.

      stepST F_9bb54 D_9bb54 (Z_to_bv 64 0xeb090) (Z_to_bv 64 3) ltac:(sok_data).
      stepb_ft F_9bb58 D_9bb58 ltac:(cond_compute).

      stepLD F_9bb5c D_9bb5c (word_to_le_bytes 8 (Z_to_bv 64 0xeb0a0)) (Z_to_bv 64 0xeb0a0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_9bb60 D_9bb60.
      stepn F_9bb64 D_9bb64.
      stepLD F_9bb68 D_9bb68 (word_to_le_bytes 8 (Z_to_bv 64 0x58968)) (Z_to_bv 64 0x58968) ltac:(addr_norm; rdn_by Mf3) ltac:(apply bytes_le_to_Z_8).
      stepLD F_9bb6c D_9bb6c (word_to_le_bytes 8 (Z_to_bv 64 0xc9668)) (Z_to_bv 64 0xc9668) ltac:(addr_norm; rdn_by Ma3) ltac:(apply bytes_le_to_Z_8).

      stepn F_9bb70 D_9bb70.
      stepn F_9bb74 D_9bb74.
      stepLD F_ad358 D_ad358 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_ad35c D_ad35c ltac:(cond_compute).
      stepret F_ad360 D_ad360 (0x9bbc4 : word) ltac:(bveq).
      stepn F_9bb78 D_9bb78.
      stepret F_9bb7c D_9bb7c (0x58968 : word) ltac:(bveq).

      stepLBU F_58910 D_58910 (Z_to_bv 8 6) ltac:(addr_norm; rdn_by Msnan).
      stepn F_58914 D_58914.
      stepb_ft F_58918 D_58918 ltac:(cond_compute).
      stepret F_5891c D_5891c (0x9bbcc : word) ltac:(bveq).

      stepn F_9bb80 D_9bb80.
      stepn F_9bb84 D_9bb84.
      stepn F_ad0d0 D_ad0d0.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_ad0d4 | reflexivity | exact D_ad0d4 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_ad0d8 D_ad0d8 ltac:(cond_compute).
      stepret F_ad2c8 D_ad2c8 (0x9bbd4 : word) ltac:(bveq).

      stepLD F_9bb88 D_9bb88 (word_to_le_bytes 4 (Z_to_bv 64 3)) (Z_to_bv 64 3)
        ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9bb8c D_9bb8c.
      stepST F_9bb90 D_9bb90 (Z_to_bv 64 0xeb090) (Z_to_bv 64 2) ltac:(sok_data).
      stepb_tk F_9bb94 D_9bb94 ltac:(cond_compute).

      stepLD F_9bb5c D_9bb5c (word_to_le_bytes 8 (Z_to_bv 64 0xeb0a0)) (Z_to_bv 64 0xeb0a0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_9bb60 D_9bb60.
      stepn F_9bb64 D_9bb64.
      stepLD F_9bb68 D_9bb68 (word_to_le_bytes 8 (Z_to_bv 64 0x58968)) (Z_to_bv 64 0x58968) ltac:(addr_norm; rdn_by Mf2) ltac:(apply bytes_le_to_Z_8).
      stepLD F_9bb6c D_9bb6c (word_to_le_bytes 8 (Z_to_bv 64 0xc9648)) (Z_to_bv 64 0xc9648) ltac:(addr_norm; rdn_by Ma2) ltac:(apply bytes_le_to_Z_8).

      stepn F_9bb70 D_9bb70.
      stepn F_9bb74 D_9bb74.
      stepLD F_ad358 D_ad358 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_ad35c D_ad35c ltac:(cond_compute).
      stepret F_ad360 D_ad360 (0x9bbc4 : word) ltac:(bveq).
      stepn F_9bb78 D_9bb78.
      stepret F_9bb7c D_9bb7c (0x58968 : word) ltac:(bveq).

      stepLBU F_58910 D_58910 (Z_to_bv 8 16) ltac:(addr_norm; rdn_by Msinf).
      stepn F_58914 D_58914.
      stepb_ft F_58918 D_58918 ltac:(cond_compute).
      stepret F_5891c D_5891c (0x9bbcc : word) ltac:(bveq).

      stepn F_9bb80 D_9bb80.
      stepn F_9bb84 D_9bb84.
      stepn F_ad0d0 D_ad0d0.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_ad0d4 | reflexivity | exact D_ad0d4 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_ad0d8 D_ad0d8 ltac:(cond_compute).
      stepret F_ad2c8 D_ad2c8 (0x9bbd4 : word) ltac:(bveq).

      stepLD F_9bb88 D_9bb88 (word_to_le_bytes 4 (Z_to_bv 64 2)) (Z_to_bv 64 2)
        ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9bb8c D_9bb8c.
      stepST F_9bb90 D_9bb90 (Z_to_bv 64 0xeb090) (Z_to_bv 64 1) ltac:(sok_data).
      stepb_tk F_9bb94 D_9bb94 ltac:(cond_compute).

      stepLD F_9bb5c D_9bb5c (word_to_le_bytes 8 (Z_to_bv 64 0xeb0a0)) (Z_to_bv 64 0xeb0a0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_9bb60 D_9bb60.
      stepn F_9bb64 D_9bb64.
      stepLD F_9bb68 D_9bb68 (word_to_le_bytes 8 (Z_to_bv 64 0x583d0)) (Z_to_bv 64 0x583d0) ltac:(addr_norm; rdn_by Mf1) ltac:(apply bytes_le_to_Z_8).
      stepLD F_9bb6c D_9bb6c (word_to_le_bytes 8 (Z_to_bv 64 0xb92f8)) (Z_to_bv 64 0xb92f8) ltac:(addr_norm; rdn_by Ma1) ltac:(apply bytes_le_to_Z_8).

      stepn F_9bb70 D_9bb70.
      stepn F_9bb74 D_9bb74.
      stepLD F_ad358 D_ad358 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_ad35c D_ad35c ltac:(cond_compute).
      stepret F_ad360 D_ad360 (0x9bbc4 : word) ltac:(bveq).
      stepn F_9bb78 D_9bb78.
      stepret F_9bb7c D_9bb7c (0x583d0 : word) ltac:(bveq).
      stepret F_58378 D_58378 (0x9bbcc : word) ltac:(bveq).

      stepn F_9bb80 D_9bb80.
      stepn F_9bb84 D_9bb84.
      stepn F_ad0d0 D_ad0d0.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_ad0d4 | reflexivity | exact D_ad0d4 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_ad0d8 D_ad0d8 ltac:(cond_compute).
      stepret F_ad2c8 D_ad2c8 (0x9bbd4 : word) ltac:(bveq).

      stepLD F_9bb88 D_9bb88 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1)
        ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9bb8c D_9bb8c.
      stepST F_9bb90 D_9bb90 (Z_to_bv 64 0xeb090) (Z_to_bv 64 0) ltac:(sok_data).
      stepb_tk F_9bb94 D_9bb94 ltac:(cond_compute).

      stepLD F_9bb5c D_9bb5c (word_to_le_bytes 8 (Z_to_bv 64 0xeb0a0)) (Z_to_bv 64 0xeb0a0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_9bb60 D_9bb60.
      stepn F_9bb64 D_9bb64.
      stepLD F_9bb68 D_9bb68 (word_to_le_bytes 8 (Z_to_bv 64 0x9bda4)) (Z_to_bv 64 0x9bda4) ltac:(addr_norm; rdn_by Mf0) ltac:(apply bytes_le_to_Z_8).
      stepLD F_9bb6c D_9bb6c (word_to_le_bytes 8 (Z_to_bv 64 0x3496c)) (Z_to_bv 64 0x3496c) ltac:(addr_norm; rdn_by Ma0) ltac:(apply bytes_le_to_Z_8).

      stepn F_9bb70 D_9bb70.
      stepn F_9bb74 D_9bb74.
      stepLD F_ad358 D_ad358 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_ad35c D_ad35c ltac:(cond_compute).
      stepret F_ad360 D_ad360 (0x9bbc4 : word) ltac:(bveq).
      stepn F_9bb78 D_9bb78.
      stepret F_9bb7c D_9bb7c (0x9bda4 : word) ltac:(bveq).

      stepret F_9bd58 D_9bd58 (0x3496c : word) ltac:(bveq).
      stepn F_34914 D_34914.
      stepLBU F_34918 D_34918 (Z_to_bv 8 0) ltac:(addr_norm; rdn_by Mcb).
      stepb_ft F_3491c D_3491c ltac:(cond_compute).
      stepret F_34920 D_34920 (0x9bbcc : word) ltac:(bveq).

      stepn F_9bb80 D_9bb80.
      stepn F_9bb84 D_9bb84.
      stepn F_ad0d0 D_ad0d0.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_ad0d4 | reflexivity | exact D_ad0d4 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_ad0d8 D_ad0d8 ltac:(cond_compute).
      stepret F_ad2c8 D_ad2c8 (0x9bbd4 : word) ltac:(bveq).

      stepLD F_9bb88 D_9bb88 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9bb8c D_9bb8c.
      stepST F_9bb90 D_9bb90 (Z_to_bv 64 0xeb090) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
      stepb_ft F_9bb94 D_9bb94 ltac:(cond_compute).

      stepLD F_9bb98 D_9bb98 (word_to_le_bytes 8 (Z_to_bv 64 0xeb0a0)) (Z_to_bv 64 0xeb0a0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_9bb9c D_9bb9c.
      stepLD F_9bb3c D_9bb3c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mnx) ltac:(apply bytes_le_to_Z_8).
      stepn F_9bb40 D_9bb40.
      stepST F_9bb44 D_9bb44 (Z_to_bv 64 0xeb090) (Z_to_bv 64 32) ltac:(sok_data).
      stepST F_9bb48 D_9bb48 (Z_to_bv 64 0xeb098) (Z_to_bv 64 0) ltac:(sok_data).
      stepb_tk F_9bb4c D_9bb4c ltac:(cond_compute).
      stepn F_9bba0 D_9bba0.
      stepST F_9bba4 D_9bba4 (Z_to_bv 64 0xeb088) (Z_to_bv 64 1) ltac:(sok_data).
      change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
      stepn F_9bba8 D_9bba8.
      stepLD8 F_9bbac D_9bbac (Z_to_bv 64 0x9be5c).
      stepLD8 F_9bbb0 D_9bbb0 code.
      stepLD8 F_9bbb4 D_9bbb4 (getr regs 9).
      stepLD8 F_9bbb8 D_9bbb8 (getr regs 18).
      stepLD8 F_9bbbc D_9bbbc (getr regs 19).
      stepn F_9bbc0 D_9bbc0. sp_renorm.

      stepn F_9bbc4 D_9bbc4.
      stepLD F_ad358 D_ad358 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_ad35c D_ad35c ltac:(cond_compute).
      stepret F_ad360 D_ad360 (0x9be5c : word) ltac:(bveq).
      stepn F_9be10 D_9be10.
      apply mst_refl.
    - repeat split; gres; try reflexivity. exact Htp. }
  {
    destruct AX as (Mxl & Mxh & Msl & Mnx & Mf0 & Ma0 & Mf1 & Ma1 & Mf2 & Ma2 & Mf3 & Ma3 & Msinf & Msnan). unfold mem_w1, ax_writes. eexists. split.
    -
      stepn F_9bdac D_9bdac. rewrite Hsp. sp_renorm.

      stepST F_9bdb0 D_9bdb0 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
      stepST F_9bdb4 D_9bdb4 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).

      stepn F_9bdb8 D_9bdb8.
      stepn F_9bdbc D_9bdbc. rewrite Htp.

      stepLD F_9bdc0 D_9bdc0 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
        ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      rewrite (v_lw_small tid) by lia.

      stepn F_9bdc4 D_9bdc4.
      stepn F_9bdc8 D_9bdc8.

      eapply mst_step; [reflexivity
        | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
          [ exact F_9bdcc | reflexivity | exact D_9bdcc
          | gres; u_norm; reflexivity
          | gres; rdn_by Mlock
          | apply bytes_le_to_Z_4; u_norm; lia ]
        | ].
      reduce_bv_eqb_ifs; norm_pc_r; vnorm.

      eapply mst_step; [reflexivity
        | eapply step_bne_ft_r; [exact F_9bdd0 | reflexivity | exact D_9bdd0 | gres; cond_compute ] | ].
      norm_pc_r.

      eapply mst_step; [reflexivity
        | eapply step_sc_w_ok; [exact F_9bdd4 | reflexivity | exact D_9bdd4
          | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
      step_simpl; vnorm.

      stepb_ft F_9bdd8 D_9bdd8 ltac:(cond_compute).

      stepn F_9bddc D_9bddc.

      stepb_ft F_9bde0 D_9bde0 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).

      stepb_tk F_9bde4 D_9bde4 ltac:(cond_compute).

      stepn F_9be08 D_9be08. rewrite Ha0.

      stepn F_9be0c D_9be0c.

      stepn F_9bb00 D_9bb00. sp_renorm.
      stepST F_9bb04 D_9bb04 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x9be5c) ltac:(sok_stack SOK).
      stepST F_9bb08 D_9bb08 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
      stepST F_9bb0c D_9bb0c (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
      stepST F_9bb10 D_9bb10 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
      stepST F_9bb14 D_9bb14 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
      stepn F_9bb18 D_9bb18. stepn F_9bb1c D_9bb1c. stepn F_9bb20 D_9bb20. stepn F_9bb24 D_9bb24.

      stepn F_9bb28 D_9bb28.
      stepn F_ad0d0 D_ad0d0.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_ad0d4 | reflexivity | exact D_ad0d4 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_ad0d8 D_ad0d8 ltac:(cond_compute).
      stepret F_ad2c8 D_ad2c8 (0x9bb78 : word) ltac:(bveq).

      stepLD F_9bb2c D_9bb2c (word_to_le_bytes 8 (Z_to_bv 64 0xeb0a0)) (Z_to_bv 64 0xeb0a0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_9bb30 D_9bb30 ltac:(cond_compute).
      stepLD F_9bb34 D_9bb34 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(addr_norm; rdn_by Msl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9bb38 D_9bb38.
      stepn F_9bb50 D_9bb50.

      stepST F_9bb54 D_9bb54 (Z_to_bv 64 0xeb090) (Z_to_bv 64 3) ltac:(sok_data).
      stepb_ft F_9bb58 D_9bb58 ltac:(cond_compute).

      stepLD F_9bb5c D_9bb5c (word_to_le_bytes 8 (Z_to_bv 64 0xeb0a0)) (Z_to_bv 64 0xeb0a0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_9bb60 D_9bb60.
      stepn F_9bb64 D_9bb64.
      stepLD F_9bb68 D_9bb68 (word_to_le_bytes 8 (Z_to_bv 64 0x583d0)) (Z_to_bv 64 0x583d0) ltac:(addr_norm; rdn_by Mf3) ltac:(apply bytes_le_to_Z_8).
      stepLD F_9bb6c D_9bb6c (word_to_le_bytes 8 (Z_to_bv 64 0xb92f8)) (Z_to_bv 64 0xb92f8) ltac:(addr_norm; rdn_by Ma3) ltac:(apply bytes_le_to_Z_8).

      stepn F_9bb70 D_9bb70.
      stepn F_9bb74 D_9bb74.
      stepLD F_ad358 D_ad358 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_ad35c D_ad35c ltac:(cond_compute).
      stepret F_ad360 D_ad360 (0x9bbc4 : word) ltac:(bveq).
      stepn F_9bb78 D_9bb78.
      stepret F_9bb7c D_9bb7c (0x583d0 : word) ltac:(bveq).
      stepret F_58378 D_58378 (0x9bbcc : word) ltac:(bveq).

      stepn F_9bb80 D_9bb80.
      stepn F_9bb84 D_9bb84.
      stepn F_ad0d0 D_ad0d0.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_ad0d4 | reflexivity | exact D_ad0d4 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_ad0d8 D_ad0d8 ltac:(cond_compute).
      stepret F_ad2c8 D_ad2c8 (0x9bbd4 : word) ltac:(bveq).

      stepLD F_9bb88 D_9bb88 (word_to_le_bytes 4 (Z_to_bv 64 3)) (Z_to_bv 64 3)
        ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9bb8c D_9bb8c.
      stepST F_9bb90 D_9bb90 (Z_to_bv 64 0xeb090) (Z_to_bv 64 2) ltac:(sok_data).
      stepb_tk F_9bb94 D_9bb94 ltac:(cond_compute).

      stepLD F_9bb5c D_9bb5c (word_to_le_bytes 8 (Z_to_bv 64 0xeb0a0)) (Z_to_bv 64 0xeb0a0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_9bb60 D_9bb60.
      stepn F_9bb64 D_9bb64.
      stepLD F_9bb68 D_9bb68 (word_to_le_bytes 8 (Z_to_bv 64 0x58968)) (Z_to_bv 64 0x58968) ltac:(addr_norm; rdn_by Mf2) ltac:(apply bytes_le_to_Z_8).
      stepLD F_9bb6c D_9bb6c (word_to_le_bytes 8 (Z_to_bv 64 0xc9668)) (Z_to_bv 64 0xc9668) ltac:(addr_norm; rdn_by Ma2) ltac:(apply bytes_le_to_Z_8).

      stepn F_9bb70 D_9bb70.
      stepn F_9bb74 D_9bb74.
      stepLD F_ad358 D_ad358 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_ad35c D_ad35c ltac:(cond_compute).
      stepret F_ad360 D_ad360 (0x9bbc4 : word) ltac:(bveq).
      stepn F_9bb78 D_9bb78.
      stepret F_9bb7c D_9bb7c (0x58968 : word) ltac:(bveq).

      stepLBU F_58910 D_58910 (Z_to_bv 8 6) ltac:(addr_norm; rdn_by Msnan).
      stepn F_58914 D_58914.
      stepb_ft F_58918 D_58918 ltac:(cond_compute).
      stepret F_5891c D_5891c (0x9bbcc : word) ltac:(bveq).

      stepn F_9bb80 D_9bb80.
      stepn F_9bb84 D_9bb84.
      stepn F_ad0d0 D_ad0d0.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_ad0d4 | reflexivity | exact D_ad0d4 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_ad0d8 D_ad0d8 ltac:(cond_compute).
      stepret F_ad2c8 D_ad2c8 (0x9bbd4 : word) ltac:(bveq).

      stepLD F_9bb88 D_9bb88 (word_to_le_bytes 4 (Z_to_bv 64 2)) (Z_to_bv 64 2)
        ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9bb8c D_9bb8c.
      stepST F_9bb90 D_9bb90 (Z_to_bv 64 0xeb090) (Z_to_bv 64 1) ltac:(sok_data).
      stepb_tk F_9bb94 D_9bb94 ltac:(cond_compute).

      stepLD F_9bb5c D_9bb5c (word_to_le_bytes 8 (Z_to_bv 64 0xeb0a0)) (Z_to_bv 64 0xeb0a0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_9bb60 D_9bb60.
      stepn F_9bb64 D_9bb64.
      stepLD F_9bb68 D_9bb68 (word_to_le_bytes 8 (Z_to_bv 64 0x58968)) (Z_to_bv 64 0x58968) ltac:(addr_norm; rdn_by Mf1) ltac:(apply bytes_le_to_Z_8).
      stepLD F_9bb6c D_9bb6c (word_to_le_bytes 8 (Z_to_bv 64 0xc9648)) (Z_to_bv 64 0xc9648) ltac:(addr_norm; rdn_by Ma1) ltac:(apply bytes_le_to_Z_8).

      stepn F_9bb70 D_9bb70.
      stepn F_9bb74 D_9bb74.
      stepLD F_ad358 D_ad358 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_ad35c D_ad35c ltac:(cond_compute).
      stepret F_ad360 D_ad360 (0x9bbc4 : word) ltac:(bveq).
      stepn F_9bb78 D_9bb78.
      stepret F_9bb7c D_9bb7c (0x58968 : word) ltac:(bveq).

      stepLBU F_58910 D_58910 (Z_to_bv 8 16) ltac:(addr_norm; rdn_by Msinf).
      stepn F_58914 D_58914.
      stepb_ft F_58918 D_58918 ltac:(cond_compute).
      stepret F_5891c D_5891c (0x9bbcc : word) ltac:(bveq).

      stepn F_9bb80 D_9bb80.
      stepn F_9bb84 D_9bb84.
      stepn F_ad0d0 D_ad0d0.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_ad0d4 | reflexivity | exact D_ad0d4 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_ad0d8 D_ad0d8 ltac:(cond_compute).
      stepret F_ad2c8 D_ad2c8 (0x9bbd4 : word) ltac:(bveq).

      stepLD F_9bb88 D_9bb88 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1)
        ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9bb8c D_9bb8c.
      stepST F_9bb90 D_9bb90 (Z_to_bv 64 0xeb090) (Z_to_bv 64 0) ltac:(sok_data).
      stepb_tk F_9bb94 D_9bb94 ltac:(cond_compute).

      stepLD F_9bb5c D_9bb5c (word_to_le_bytes 8 (Z_to_bv 64 0xeb0a0)) (Z_to_bv 64 0xeb0a0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_9bb60 D_9bb60.
      stepn F_9bb64 D_9bb64.
      stepLD F_9bb68 D_9bb68 (word_to_le_bytes 8 (Z_to_bv 64 0x9bda4)) (Z_to_bv 64 0x9bda4) ltac:(addr_norm; rdn_by Mf0) ltac:(apply bytes_le_to_Z_8).
      stepLD F_9bb6c D_9bb6c (word_to_le_bytes 8 (Z_to_bv 64 0x3496c)) (Z_to_bv 64 0x3496c) ltac:(addr_norm; rdn_by Ma0) ltac:(apply bytes_le_to_Z_8).

      stepn F_9bb70 D_9bb70.
      stepn F_9bb74 D_9bb74.
      stepLD F_ad358 D_ad358 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_ad35c D_ad35c ltac:(cond_compute).
      stepret F_ad360 D_ad360 (0x9bbc4 : word) ltac:(bveq).
      stepn F_9bb78 D_9bb78.
      stepret F_9bb7c D_9bb7c (0x9bda4 : word) ltac:(bveq).

      stepret F_9bd58 D_9bd58 (0x3496c : word) ltac:(bveq).
      stepn F_34914 D_34914.
      stepLBU F_34918 D_34918 (Z_to_bv 8 0) ltac:(addr_norm; rdn_by Mcb).
      stepb_ft F_3491c D_3491c ltac:(cond_compute).
      stepret F_34920 D_34920 (0x9bbcc : word) ltac:(bveq).

      stepn F_9bb80 D_9bb80.
      stepn F_9bb84 D_9bb84.
      stepn F_ad0d0 D_ad0d0.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_ad0d4 | reflexivity | exact D_ad0d4 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_ad0d8 D_ad0d8 ltac:(cond_compute).
      stepret F_ad2c8 D_ad2c8 (0x9bbd4 : word) ltac:(bveq).

      stepLD F_9bb88 D_9bb88 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9bb8c D_9bb8c.
      stepST F_9bb90 D_9bb90 (Z_to_bv 64 0xeb090) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
      stepb_ft F_9bb94 D_9bb94 ltac:(cond_compute).

      stepLD F_9bb98 D_9bb98 (word_to_le_bytes 8 (Z_to_bv 64 0xeb0a0)) (Z_to_bv 64 0xeb0a0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_9bb9c D_9bb9c.
      stepLD F_9bb3c D_9bb3c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mnx) ltac:(apply bytes_le_to_Z_8).
      stepn F_9bb40 D_9bb40.
      stepST F_9bb44 D_9bb44 (Z_to_bv 64 0xeb090) (Z_to_bv 64 32) ltac:(sok_data).
      stepST F_9bb48 D_9bb48 (Z_to_bv 64 0xeb098) (Z_to_bv 64 0) ltac:(sok_data).
      stepb_tk F_9bb4c D_9bb4c ltac:(cond_compute).
      stepn F_9bba0 D_9bba0.
      stepST F_9bba4 D_9bba4 (Z_to_bv 64 0xeb088) (Z_to_bv 64 1) ltac:(sok_data).
      change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
      stepn F_9bba8 D_9bba8.
      stepLD8 F_9bbac D_9bbac (Z_to_bv 64 0x9be5c).
      stepLD8 F_9bbb0 D_9bbb0 code.
      stepLD8 F_9bbb4 D_9bbb4 (getr regs 9).
      stepLD8 F_9bbb8 D_9bbb8 (getr regs 18).
      stepLD8 F_9bbbc D_9bbbc (getr regs 19).
      stepn F_9bbc0 D_9bbc0. sp_renorm.

      stepn F_9bbc4 D_9bbc4.
      stepLD F_ad358 D_ad358 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_ad35c D_ad35c ltac:(cond_compute).
      stepret F_ad360 D_ad360 (0x9be5c : word) ltac:(bveq).
      stepn F_9be10 D_9be10.
      apply mst_refl.
    - repeat split; gres; try reflexivity. exact Htp. }
Qed.

Definition mem_w2 (mem : word -> option byte) (sp code s1v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x9be60)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x9bddc)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0xb24f8)))
    (Z_to_bv 64 0xb9608) [Z_to_bv 8 1].

Lemma w2 : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x9be60 -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0xb82a8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb2500)) ->
  rdn RSEGS mem (Z_to_bv 64 0xb82b0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb24f8)) ->
  rdn RSEGS mem (Z_to_bv 64 0xb24f8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x344b4)) ->
  rdn RSEGS mem (Z_to_bv 64 0xb9608) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0xb8138) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x9bc14)) ->
  rdn RSEGS mem (Z_to_bv 64 0xb92d0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb92d0)) ->
  rdn RSEGS mem (Z_to_bv 64 0xb8140) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x9bdac : word) mem rom)
                 (mkst regs' (0xa149c : word) (mem_w2 mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x9be64
    /\ getr regs' 9 = s1v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hra Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mdso Mg2.
  unfold mem_w2. eexists. split.
  -
    stepn F_9bd60 D_9bd60. rewrite Hsp. sp_renorm.
    stepST F_9bd64 D_9bd64 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x9be60) ltac:(sok_stack SOK).
    stepST F_9bd68 D_9bd68 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_9bd6c D_9bd6c (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).

    stepn F_9bd70 D_9bd70.
    stepn F_9bd74 D_9bd74.
    stepLD8 F_9bd78 D_9bd78 (Z_to_bv 64 0xb2500).
    stepLD8 F_9bd7c D_9bd7c (Z_to_bv 64 0xb24f8).

    stepb_ft F_9bd80 D_9bd80 ltac:(cond_compute).

    stepLD8 F_9bd84 D_9bd84 (Z_to_bv 64 0x344b4).
    stepn F_9bd88 D_9bd88.
    stepjr F_9bd8c D_9bd8c (Z_to_bv 64 0x344b4) ltac:(gres; reflexivity). vnorm.

    stepn F_3445c D_3445c. sp_renorm.
    stepST F_34460 D_34460 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x9bddc) ltac:(sok_stack SOK).
    stepST F_34464 D_34464 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0xb24f8) ltac:(sok_stack SOK).
    stepn F_34468 D_34468.
    stepn F_3446c D_3446c.
    stepn F_34470 D_34470.

    stepLBU F_34474 D_34474 (Z_to_bv 8 0) ltac:(rewrite v_addi_0; rdn_by Mcomp).
    stepn F_34478 D_34478.
    stepb_tk F_3447c D_3447c ltac:(cond_compute).
    stepn F_34488 D_34488.
    stepn F_3448c D_3448c.
    stepn F_34490 D_34490.

    stepST F_34494 D_34494 (Z_to_bv 64 0xb9608) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).

    stepn F_34498 D_34498.
    stepLD8 F_3449c D_3449c (Z_to_bv 64 0x9bc14).

    stepb_ft F_344a0 D_344a0 ltac:(cond_compute).
    stepn F_344a4 D_344a4.
    stepn F_344a8 D_344a8.
    stepn F_344ac D_344ac.
    stepLD8 F_344b0 D_344b0 (Z_to_bv 64 0xb92d0).
    stepn F_344b4 D_344b4.
    stepret F_9bbc8 D_9bbc8 (0x34510 : word) ltac:(bveq).
    stepn F_344b8 D_344b8.

    stepn F_344bc D_344bc.
    stepLD8 F_344c0 D_344c0 (Z_to_bv 64 0).
    stepb_tk F_344c4 D_344c4 ltac:(cond_compute).

    stepLD8 F_344dc D_344dc (Z_to_bv 64 0x9bddc).
    stepLD8 F_344e0 D_344e0 (Z_to_bv 64 0xb24f8).
    stepn F_344e4 D_344e4. sp_renorm.
    stepret F_344e8 D_344e8 (0x9bddc : word) ltac:(bveq).

    stepn F_9bd90 D_9bd90.
    stepb_ft F_9bd94 D_9bd94 ltac:(cond_compute).
    stepLD8 F_9bd98 D_9bd98 (Z_to_bv 64 0x9be60).
    stepLD8 F_9bd9c D_9bd9c code.
    stepLD8 F_9bda0 D_9bda0 s1v.
    stepn F_9bda4 D_9bda4. sp_renorm.

    stepn F_9bda8 D_9bda8.
    stepret F_9bd5c D_9bd5c (0x9be60 : word) ltac:(bveq).
    stepn F_9be14 D_9be14.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
