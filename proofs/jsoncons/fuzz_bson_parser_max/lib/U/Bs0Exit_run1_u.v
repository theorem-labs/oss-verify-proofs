(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
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
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0ExitBase_u Bs0_code_99768_9976c_u Bs0_code_34324_34354_u Bs0_code_56d4c_56d5c_u Bs0_code_r1ff24_20000_u Bs0_code_r20000_21000_u Bs0_code_r4b000_4c000_u Bs0_code_r4d000_4e000_u Bs0_code_r55a7c_55a80_u Bs0_code_r98734_98800_u Bs0_code_ra9ec0_a9ecc_u Bs0_code_r988c8_988cc_u Bs0_code_r33a9c_33b2c_u Bs0_code_r58000_59000_u     .
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
Inductive axv : Type := AX0 | AXg | AXgc | AXgs | AXgcs | AXgsc.
Definition atexit_cells (mem : word -> option byte) (ax : axv) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0xea00c) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0))
  /\ match ax with
     | AX0 => rdn RSEGS mem (Z_to_bv 64 0xea018) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
     | AXg => rdn RSEGS mem (Z_to_bv 64 0xea018) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xea020))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea010) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea020) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea028) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x9ad9c))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea128) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x346a4))
     | AXgc => rdn RSEGS mem (Z_to_bv 64 0xea018) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xea020))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea010) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 2))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea020) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea028) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x9ad9c))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea128) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x346a4))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea030) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x57e98))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea130) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb8240))
     | AXgs => rdn RSEGS mem (Z_to_bv 64 0xea018) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xea020))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea010) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 3))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea020) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea028) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x9ad9c))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea128) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x346a4))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea030) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x58430))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea130) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xc8588))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea038) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x58430))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea138) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xc85a8))
         /\ rdn RSEGS mem (Z_to_bv 64 0xc8588) 1%nat = Some [Z_to_bv 8 16]
         /\ rdn RSEGS mem (Z_to_bv 64 0xc85a8) 1%nat = Some [Z_to_bv 8 6]
     | AXgcs => rdn RSEGS mem (Z_to_bv 64 0xea018) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xea020))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea010) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea020) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea028) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x9ad9c))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea128) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x346a4))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea030) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x57e98))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea130) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb8240))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea038) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x58430))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea138) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xc8588))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea040) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x58430))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea140) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xc85a8))
         /\ rdn RSEGS mem (Z_to_bv 64 0xc8588) 1%nat = Some [Z_to_bv 8 16]
         /\ rdn RSEGS mem (Z_to_bv 64 0xc85a8) 1%nat = Some [Z_to_bv 8 6]
     | AXgsc => rdn RSEGS mem (Z_to_bv 64 0xea018) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xea020))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea010) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea020) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea028) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x9ad9c))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea128) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x346a4))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea030) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x58430))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea130) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xc8588))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea038) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x58430))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea138) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xc85a8))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea040) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x57e98))
         /\ rdn RSEGS mem (Z_to_bv 64 0xea140) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb8240))
         /\ rdn RSEGS mem (Z_to_bv 64 0xc8588) 1%nat = Some [Z_to_bv 8 16]
         /\ rdn RSEGS mem (Z_to_bv 64 0xc85a8) 1%nat = Some [Z_to_bv 8 6]
     end.

(* [comment removed for export] *)
Lemma atexit_cells_frame : forall (M M' : word -> option byte) (ax : axv),
  (forall a : Z, ((0xea008 <= a < 0xea228) \/ (0xc8588 <= a < 0xc8589) \/ (0xc85a8 <= a < 0xc85a9))%Z -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> atexit_cells M ax -> atexit_cells M' ax.
Proof.
  intros M M' ax AG H.
  assert (R : forall (a : Z) (n : nat) v, (0 <= a)%Z -> (a + Z.of_nat n <= 0xea228)%Z ->
             (forall x : Z, (a <= x < a + Z.of_nat n)%Z -> ((0xea008 <= x < 0xea228) \/ (0xc8588 <= x < 0xc8589) \/ (0xc85a8 <= x < 0xc85a9))%Z) -> rdn RSEGS M (Z_to_bv 64 a) n = v -> rdn RSEGS M' (Z_to_bv 64 a) n = v).
  { intros a n v H1 H2 HF <-. apply rdn_ext; [rewrite u_Z2bv by lia; lia|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
    rewrite <- (Z_to_bv_bv_unsigned 64 x). apply AG. apply HF. lia. }
  unfold atexit_cells in *. destruct H as (H0 & H).
  split; [apply R; [lia | cbn; lia | intros x Hx; cbn in Hx; lia | exact H0]|].
  destruct ax; repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end;
    repeat split; (apply R; [lia | cbn; lia | intros x Hx; cbn in Hx; lia | assumption]).
Qed.

Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ax_writes (ax : axv) (m : word -> option byte) : word -> option byte :=
  match ax with
  | AX0 => m
  | AXg => wbytes (wbytes (wbytes (wbytes (m)
      (Z_to_bv 64 0xea010) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 0xea010) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
      (Z_to_bv 64 0xea010) (word_to_le_bytes 4 (Z_to_bv 64 32)))
      (Z_to_bv 64 0xea018) (word_to_le_bytes 8 (Z_to_bv 64 0))
  | AXgc => wbytes (wbytes (wbytes (wbytes (wbytes (m)
      (Z_to_bv 64 0xea010) (word_to_le_bytes 4 (Z_to_bv 64 1)))
      (Z_to_bv 64 0xea010) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 0xea010) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
      (Z_to_bv 64 0xea010) (word_to_le_bytes 4 (Z_to_bv 64 32)))
      (Z_to_bv 64 0xea018) (word_to_le_bytes 8 (Z_to_bv 64 0))
  | AXgs => wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m)
      (Z_to_bv 64 0xea010) (word_to_le_bytes 4 (Z_to_bv 64 2)))
      (Z_to_bv 64 0xea010) (word_to_le_bytes 4 (Z_to_bv 64 1)))
      (Z_to_bv 64 0xea010) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 0xea010) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
      (Z_to_bv 64 0xea010) (word_to_le_bytes 4 (Z_to_bv 64 32)))
      (Z_to_bv 64 0xea018) (word_to_le_bytes 8 (Z_to_bv 64 0))
  | AXgcs => wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m)
      (Z_to_bv 64 0xea010) (word_to_le_bytes 4 (Z_to_bv 64 3)))
      (Z_to_bv 64 0xea010) (word_to_le_bytes 4 (Z_to_bv 64 2)))
      (Z_to_bv 64 0xea010) (word_to_le_bytes 4 (Z_to_bv 64 1)))
      (Z_to_bv 64 0xea010) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 0xea010) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
      (Z_to_bv 64 0xea010) (word_to_le_bytes 4 (Z_to_bv 64 32)))
      (Z_to_bv 64 0xea018) (word_to_le_bytes 8 (Z_to_bv 64 0))
  | AXgsc => wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m)
      (Z_to_bv 64 0xea010) (word_to_le_bytes 4 (Z_to_bv 64 3)))
      (Z_to_bv 64 0xea010) (word_to_le_bytes 4 (Z_to_bv 64 2)))
      (Z_to_bv 64 0xea010) (word_to_le_bytes 4 (Z_to_bv 64 1)))
      (Z_to_bv 64 0xea010) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 0xea010) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
      (Z_to_bv 64 0xea010) (word_to_le_bytes 4 (Z_to_bv 64 32)))
      (Z_to_bv 64 0xea018) (word_to_le_bytes 8 (Z_to_bv 64 0))
  end.
Definition mem_w1 (ax : axv) (mem : word -> option byte) (sp ra s0 : word) (tid : Z) (code s1 s2 s3 : word) :=
  wbytes (ax_writes ax (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (bv_unsigned sp - 16)) (word_to_le_bytes 8 s0))
    (Z_to_bv 64 0xea228) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x9ae54)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3)))
    (Z_to_bv 64 0xea008) [Z_to_bv 8 1].

Lemma w1 : forall (ax : axv) regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn RSEGS mem (Z_to_bv 64 0xea228) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  stdio_globals mem ->
  rdn RSEGS mem (Z_to_bv 64 0xc8554) 1%nat = Some [Z_to_bv 8 0] ->      (* [comment removed for export] *)
  atexit_cells mem ax ->
  exists regs',
    msteps RSEGS (mkst regs (0x9adf0 : word) mem rom)
                 (mkst regs' (0x9ada4 : word) (mem_w1 ax mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x9ae58
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros ax regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock GL Mcb AX.
  destruct GL as (Gnl & _).
  destruct ax.
  { (* [comment removed for export] *)
    destruct AX as (Mxl & Mxh). unfold mem_w1, ax_writes. eexists. split.
    - (* [comment removed for export] *)
      stepn F_997bc D_997bc. rewrite Hsp. sp_renorm.
      (* [comment removed for export] *)
      stepST F_997c0 D_997c0 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
      stepST F_997c4 D_997c4 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
      (* [comment removed for export] *)
      stepn F_997c8 D_997c8.
      stepn F_997cc D_997cc. rewrite Htp.
      (* [comment removed for export] *)
      stepLD F_997d0 D_997d0 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
        ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      rewrite (v_lw_small tid) by lia.
      (* [comment removed for export] *)
      stepn F_997d4 D_997d4.
      stepn F_997d8 D_997d8.
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity
        | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
          [ exact F_997dc | reflexivity | exact D_997dc
          | gres; u_norm; reflexivity
          | gres; rdn_by Mlock
          | apply bytes_le_to_Z_4; u_norm; lia ]
        | ].
      reduce_bv_eqb_ifs; norm_pc_r; vnorm.
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity
        | eapply step_bne_ft_r; [exact F_997e0 | reflexivity | exact D_997e0 | gres; cond_compute ] | ].
      norm_pc_r.
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity
        | eapply step_sc_w_ok; [exact F_997e4 | reflexivity | exact D_997e4
          | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
      step_simpl; vnorm.
      (* [comment removed for export] *)
      stepb_ft F_997e8 D_997e8 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepn F_997ec D_997ec.
      (* [comment removed for export] *)
      stepb_ft F_997f0 D_997f0 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
      (* [comment removed for export] *)
      stepb_tk F_997f4 D_997f4 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepn F_99818 D_99818. rewrite Ha0.
      (* [comment removed for export] *)
      stepn F_9981c D_9981c.
      (* [comment removed for export] *)
      stepn F_99510 D_99510. sp_renorm.
      stepST F_99514 D_99514 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x9ae54) ltac:(sok_stack SOK).
      stepST F_99518 D_99518 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
      stepST F_9951c D_9951c (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
      stepST F_99520 D_99520 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
      stepST F_99524 D_99524 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
      stepn F_99528 D_99528. stepn F_9952c D_9952c. stepn F_99530 D_99530. stepn F_99534 D_99534.
      (* [comment removed for export] *)
      stepn F_99538 D_99538.
      stepn F_aaadc D_aaadc.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_aaae0 | reflexivity | exact D_aaae0 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_aaae4 D_aaae4 ltac:(cond_compute).
      stepret F_aacd4 D_aacd4 (0x9ab70 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepLD F_9953c D_9953c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepb_tk F_99540 D_99540 ltac:(cond_compute).
      stepn F_995b0 D_995b0.
      stepST F_995b4 D_995b4 (Z_to_bv 64 0xea008) (Z_to_bv 64 1) ltac:(sok_data).
      change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
      stepn F_995b8 D_995b8.
      stepLD8 F_995bc D_995bc (Z_to_bv 64 0x9ae54).
      stepLD8 F_995c0 D_995c0 code.
      stepLD8 F_995c4 D_995c4 (getr regs 9).
      stepLD8 F_995c8 D_995c8 (getr regs 18).
      stepLD8 F_995cc D_995cc (getr regs 19).
      stepn F_995d0 D_995d0. sp_renorm.
      (* [comment removed for export] *)
      stepn F_995d4 D_995d4.
      stepLD F_aad64 D_aad64 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_aad68 D_aad68 ltac:(cond_compute).
      stepret F_aad6c D_aad6c (0x9ae54 : word) ltac:(bveq).
      stepn F_99820 D_99820.
      apply mst_refl.
    - repeat split; gres; try reflexivity. exact Htp. }
  { (* [comment removed for export] *)
    destruct AX as (Mxl & Mxh & Msl & Mnx & Mf0 & Ma0). unfold mem_w1, ax_writes. eexists. split.
    - (* [comment removed for export] *)
      stepn F_997bc D_997bc. rewrite Hsp. sp_renorm.
      (* [comment removed for export] *)
      stepST F_997c0 D_997c0 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
      stepST F_997c4 D_997c4 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
      (* [comment removed for export] *)
      stepn F_997c8 D_997c8.
      stepn F_997cc D_997cc. rewrite Htp.
      (* [comment removed for export] *)
      stepLD F_997d0 D_997d0 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
        ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      rewrite (v_lw_small tid) by lia.
      (* [comment removed for export] *)
      stepn F_997d4 D_997d4.
      stepn F_997d8 D_997d8.
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity
        | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
          [ exact F_997dc | reflexivity | exact D_997dc
          | gres; u_norm; reflexivity
          | gres; rdn_by Mlock
          | apply bytes_le_to_Z_4; u_norm; lia ]
        | ].
      reduce_bv_eqb_ifs; norm_pc_r; vnorm.
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity
        | eapply step_bne_ft_r; [exact F_997e0 | reflexivity | exact D_997e0 | gres; cond_compute ] | ].
      norm_pc_r.
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity
        | eapply step_sc_w_ok; [exact F_997e4 | reflexivity | exact D_997e4
          | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
      step_simpl; vnorm.
      (* [comment removed for export] *)
      stepb_ft F_997e8 D_997e8 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepn F_997ec D_997ec.
      (* [comment removed for export] *)
      stepb_ft F_997f0 D_997f0 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
      (* [comment removed for export] *)
      stepb_tk F_997f4 D_997f4 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepn F_99818 D_99818. rewrite Ha0.
      (* [comment removed for export] *)
      stepn F_9981c D_9981c.
      (* [comment removed for export] *)
      stepn F_99510 D_99510. sp_renorm.
      stepST F_99514 D_99514 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x9ae54) ltac:(sok_stack SOK).
      stepST F_99518 D_99518 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
      stepST F_9951c D_9951c (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
      stepST F_99520 D_99520 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
      stepST F_99524 D_99524 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
      stepn F_99528 D_99528. stepn F_9952c D_9952c. stepn F_99530 D_99530. stepn F_99534 D_99534.
      (* [comment removed for export] *)
      stepn F_99538 D_99538.
      stepn F_aaadc D_aaadc.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_aaae0 | reflexivity | exact D_aaae0 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_aaae4 D_aaae4 ltac:(cond_compute).
      stepret F_aacd4 D_aacd4 (0x9ab70 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepLD F_9953c D_9953c (word_to_le_bytes 8 (Z_to_bv 64 0xea020)) (Z_to_bv 64 0xea020) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_99540 D_99540 ltac:(cond_compute).
      stepLD F_99544 D_99544 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(addr_norm; rdn_by Msl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_99548 D_99548.
      stepn F_99560 D_99560.
      (* [comment removed for export] *)
      stepST F_99564 D_99564 (Z_to_bv 64 0xea010) (Z_to_bv 64 0) ltac:(sok_data).
      stepb_ft F_99568 D_99568 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepLD F_9956c D_9956c (word_to_le_bytes 8 (Z_to_bv 64 0xea020)) (Z_to_bv 64 0xea020) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_99570 D_99570.
      stepn F_99574 D_99574.
      stepLD F_99578 D_99578 (word_to_le_bytes 8 (Z_to_bv 64 0x9ad9c)) (Z_to_bv 64 0x9ad9c) ltac:(addr_norm; rdn_by Mf0) ltac:(apply bytes_le_to_Z_8).
      stepLD F_9957c D_9957c (word_to_le_bytes 8 (Z_to_bv 64 0x346a4)) (Z_to_bv 64 0x346a4) ltac:(addr_norm; rdn_by Ma0) ltac:(apply bytes_le_to_Z_8).
      (* [comment removed for export] *)
      stepn F_99580 D_99580.
      stepn F_99584 D_99584.
      stepLD F_aad64 D_aad64 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_aad68 D_aad68 ltac:(cond_compute).
      stepret F_aad6c D_aad6c (0x9abbc : word) ltac:(bveq).
      stepn F_99588 D_99588.
      stepret F_9958c D_9958c (0x9ad9c : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepret F_99768 D_99768 (0x346a4 : word) ltac:(bveq).
      stepn F_34324 D_34324.
      stepLBU F_34328 D_34328 (Z_to_bv 8 0) ltac:(addr_norm; rdn_by Mcb).
      stepb_ft F_3432c D_3432c ltac:(cond_compute).
      stepret F_34330 D_34330 (0x9abc4 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepn F_99590 D_99590.
      stepn F_99594 D_99594.
      stepn F_aaadc D_aaadc.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_aaae0 | reflexivity | exact D_aaae0 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_aaae4 D_aaae4 ltac:(cond_compute).
      stepret F_aacd4 D_aacd4 (0x9abcc : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepLD F_99598 D_99598 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9959c D_9959c.
      stepST F_995a0 D_995a0 (Z_to_bv 64 0xea010) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
      stepb_ft F_995a4 D_995a4 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepLD F_995a8 D_995a8 (word_to_le_bytes 8 (Z_to_bv 64 0xea020)) (Z_to_bv 64 0xea020) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_995ac D_995ac.
      stepLD F_9954c D_9954c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mnx) ltac:(apply bytes_le_to_Z_8).
      stepn F_99550 D_99550.
      stepST F_99554 D_99554 (Z_to_bv 64 0xea010) (Z_to_bv 64 32) ltac:(sok_data).
      stepST F_99558 D_99558 (Z_to_bv 64 0xea018) (Z_to_bv 64 0) ltac:(sok_data).
      stepb_tk F_9955c D_9955c ltac:(cond_compute).
      stepn F_995b0 D_995b0.
      stepST F_995b4 D_995b4 (Z_to_bv 64 0xea008) (Z_to_bv 64 1) ltac:(sok_data).
      change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
      stepn F_995b8 D_995b8.
      stepLD8 F_995bc D_995bc (Z_to_bv 64 0x9ae54).
      stepLD8 F_995c0 D_995c0 code.
      stepLD8 F_995c4 D_995c4 (getr regs 9).
      stepLD8 F_995c8 D_995c8 (getr regs 18).
      stepLD8 F_995cc D_995cc (getr regs 19).
      stepn F_995d0 D_995d0. sp_renorm.
      (* [comment removed for export] *)
      stepn F_995d4 D_995d4.
      stepLD F_aad64 D_aad64 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_aad68 D_aad68 ltac:(cond_compute).
      stepret F_aad6c D_aad6c (0x9ae54 : word) ltac:(bveq).
      stepn F_99820 D_99820.
      apply mst_refl.
    - repeat split; gres; try reflexivity. exact Htp. }
  { (* [comment removed for export] *)
    destruct AX as (Mxl & Mxh & Msl & Mnx & Mf0 & Ma0 & Mf1 & Ma1). unfold mem_w1, ax_writes. eexists. split.
    - (* [comment removed for export] *)
      stepn F_997bc D_997bc. rewrite Hsp. sp_renorm.
      (* [comment removed for export] *)
      stepST F_997c0 D_997c0 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
      stepST F_997c4 D_997c4 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
      (* [comment removed for export] *)
      stepn F_997c8 D_997c8.
      stepn F_997cc D_997cc. rewrite Htp.
      (* [comment removed for export] *)
      stepLD F_997d0 D_997d0 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
        ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      rewrite (v_lw_small tid) by lia.
      (* [comment removed for export] *)
      stepn F_997d4 D_997d4.
      stepn F_997d8 D_997d8.
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity
        | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
          [ exact F_997dc | reflexivity | exact D_997dc
          | gres; u_norm; reflexivity
          | gres; rdn_by Mlock
          | apply bytes_le_to_Z_4; u_norm; lia ]
        | ].
      reduce_bv_eqb_ifs; norm_pc_r; vnorm.
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity
        | eapply step_bne_ft_r; [exact F_997e0 | reflexivity | exact D_997e0 | gres; cond_compute ] | ].
      norm_pc_r.
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity
        | eapply step_sc_w_ok; [exact F_997e4 | reflexivity | exact D_997e4
          | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
      step_simpl; vnorm.
      (* [comment removed for export] *)
      stepb_ft F_997e8 D_997e8 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepn F_997ec D_997ec.
      (* [comment removed for export] *)
      stepb_ft F_997f0 D_997f0 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
      (* [comment removed for export] *)
      stepb_tk F_997f4 D_997f4 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepn F_99818 D_99818. rewrite Ha0.
      (* [comment removed for export] *)
      stepn F_9981c D_9981c.
      (* [comment removed for export] *)
      stepn F_99510 D_99510. sp_renorm.
      stepST F_99514 D_99514 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x9ae54) ltac:(sok_stack SOK).
      stepST F_99518 D_99518 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
      stepST F_9951c D_9951c (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
      stepST F_99520 D_99520 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
      stepST F_99524 D_99524 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
      stepn F_99528 D_99528. stepn F_9952c D_9952c. stepn F_99530 D_99530. stepn F_99534 D_99534.
      (* [comment removed for export] *)
      stepn F_99538 D_99538.
      stepn F_aaadc D_aaadc.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_aaae0 | reflexivity | exact D_aaae0 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_aaae4 D_aaae4 ltac:(cond_compute).
      stepret F_aacd4 D_aacd4 (0x9ab70 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepLD F_9953c D_9953c (word_to_le_bytes 8 (Z_to_bv 64 0xea020)) (Z_to_bv 64 0xea020) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_99540 D_99540 ltac:(cond_compute).
      stepLD F_99544 D_99544 (word_to_le_bytes 4 (Z_to_bv 64 2)) (Z_to_bv 64 2) ltac:(addr_norm; rdn_by Msl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_99548 D_99548.
      stepn F_99560 D_99560.
      (* [comment removed for export] *)
      stepST F_99564 D_99564 (Z_to_bv 64 0xea010) (Z_to_bv 64 1) ltac:(sok_data).
      stepb_ft F_99568 D_99568 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepLD F_9956c D_9956c (word_to_le_bytes 8 (Z_to_bv 64 0xea020)) (Z_to_bv 64 0xea020) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_99570 D_99570.
      stepn F_99574 D_99574.
      stepLD F_99578 D_99578 (word_to_le_bytes 8 (Z_to_bv 64 0x57e98)) (Z_to_bv 64 0x57e98) ltac:(addr_norm; rdn_by Mf1) ltac:(apply bytes_le_to_Z_8).
      stepLD F_9957c D_9957c (word_to_le_bytes 8 (Z_to_bv 64 0xb8240)) (Z_to_bv 64 0xb8240) ltac:(addr_norm; rdn_by Ma1) ltac:(apply bytes_le_to_Z_8).
      (* [comment removed for export] *)
      stepn F_99580 D_99580.
      stepn F_99584 D_99584.
      stepLD F_aad64 D_aad64 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_aad68 D_aad68 ltac:(cond_compute).
      stepret F_aad6c D_aad6c (0x9abbc : word) ltac:(bveq).
      stepn F_99588 D_99588.
      stepret F_9958c D_9958c (0x57e98 : word) ltac:(bveq).
      stepret F_56858 D_56858 (0x9abc4 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepn F_99590 D_99590.
      stepn F_99594 D_99594.
      stepn F_aaadc D_aaadc.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_aaae0 | reflexivity | exact D_aaae0 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_aaae4 D_aaae4 ltac:(cond_compute).
      stepret F_aacd4 D_aacd4 (0x9abcc : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepLD F_99598 D_99598 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1)
        ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9959c D_9959c.
      stepST F_995a0 D_995a0 (Z_to_bv 64 0xea010) (Z_to_bv 64 0) ltac:(sok_data).
      stepb_tk F_995a4 D_995a4 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepLD F_9956c D_9956c (word_to_le_bytes 8 (Z_to_bv 64 0xea020)) (Z_to_bv 64 0xea020) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_99570 D_99570.
      stepn F_99574 D_99574.
      stepLD F_99578 D_99578 (word_to_le_bytes 8 (Z_to_bv 64 0x9ad9c)) (Z_to_bv 64 0x9ad9c) ltac:(addr_norm; rdn_by Mf0) ltac:(apply bytes_le_to_Z_8).
      stepLD F_9957c D_9957c (word_to_le_bytes 8 (Z_to_bv 64 0x346a4)) (Z_to_bv 64 0x346a4) ltac:(addr_norm; rdn_by Ma0) ltac:(apply bytes_le_to_Z_8).
      (* [comment removed for export] *)
      stepn F_99580 D_99580.
      stepn F_99584 D_99584.
      stepLD F_aad64 D_aad64 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_aad68 D_aad68 ltac:(cond_compute).
      stepret F_aad6c D_aad6c (0x9abbc : word) ltac:(bveq).
      stepn F_99588 D_99588.
      stepret F_9958c D_9958c (0x9ad9c : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepret F_99768 D_99768 (0x346a4 : word) ltac:(bveq).
      stepn F_34324 D_34324.
      stepLBU F_34328 D_34328 (Z_to_bv 8 0) ltac:(addr_norm; rdn_by Mcb).
      stepb_ft F_3432c D_3432c ltac:(cond_compute).
      stepret F_34330 D_34330 (0x9abc4 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepn F_99590 D_99590.
      stepn F_99594 D_99594.
      stepn F_aaadc D_aaadc.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_aaae0 | reflexivity | exact D_aaae0 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_aaae4 D_aaae4 ltac:(cond_compute).
      stepret F_aacd4 D_aacd4 (0x9abcc : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepLD F_99598 D_99598 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9959c D_9959c.
      stepST F_995a0 D_995a0 (Z_to_bv 64 0xea010) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
      stepb_ft F_995a4 D_995a4 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepLD F_995a8 D_995a8 (word_to_le_bytes 8 (Z_to_bv 64 0xea020)) (Z_to_bv 64 0xea020) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_995ac D_995ac.
      stepLD F_9954c D_9954c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mnx) ltac:(apply bytes_le_to_Z_8).
      stepn F_99550 D_99550.
      stepST F_99554 D_99554 (Z_to_bv 64 0xea010) (Z_to_bv 64 32) ltac:(sok_data).
      stepST F_99558 D_99558 (Z_to_bv 64 0xea018) (Z_to_bv 64 0) ltac:(sok_data).
      stepb_tk F_9955c D_9955c ltac:(cond_compute).
      stepn F_995b0 D_995b0.
      stepST F_995b4 D_995b4 (Z_to_bv 64 0xea008) (Z_to_bv 64 1) ltac:(sok_data).
      change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
      stepn F_995b8 D_995b8.
      stepLD8 F_995bc D_995bc (Z_to_bv 64 0x9ae54).
      stepLD8 F_995c0 D_995c0 code.
      stepLD8 F_995c4 D_995c4 (getr regs 9).
      stepLD8 F_995c8 D_995c8 (getr regs 18).
      stepLD8 F_995cc D_995cc (getr regs 19).
      stepn F_995d0 D_995d0. sp_renorm.
      (* [comment removed for export] *)
      stepn F_995d4 D_995d4.
      stepLD F_aad64 D_aad64 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_aad68 D_aad68 ltac:(cond_compute).
      stepret F_aad6c D_aad6c (0x9ae54 : word) ltac:(bveq).
      stepn F_99820 D_99820.
      apply mst_refl.
    - repeat split; gres; try reflexivity. exact Htp. }
  { (* [comment removed for export] *)
    destruct AX as (Mxl & Mxh & Msl & Mnx & Mf0 & Ma0 & Mf1 & Ma1 & Mf2 & Ma2 & Msinf & Msnan). unfold mem_w1, ax_writes. eexists. split.
    - (* [comment removed for export] *)
      stepn F_997bc D_997bc. rewrite Hsp. sp_renorm.
      (* [comment removed for export] *)
      stepST F_997c0 D_997c0 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
      stepST F_997c4 D_997c4 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
      (* [comment removed for export] *)
      stepn F_997c8 D_997c8.
      stepn F_997cc D_997cc. rewrite Htp.
      (* [comment removed for export] *)
      stepLD F_997d0 D_997d0 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
        ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      rewrite (v_lw_small tid) by lia.
      (* [comment removed for export] *)
      stepn F_997d4 D_997d4.
      stepn F_997d8 D_997d8.
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity
        | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
          [ exact F_997dc | reflexivity | exact D_997dc
          | gres; u_norm; reflexivity
          | gres; rdn_by Mlock
          | apply bytes_le_to_Z_4; u_norm; lia ]
        | ].
      reduce_bv_eqb_ifs; norm_pc_r; vnorm.
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity
        | eapply step_bne_ft_r; [exact F_997e0 | reflexivity | exact D_997e0 | gres; cond_compute ] | ].
      norm_pc_r.
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity
        | eapply step_sc_w_ok; [exact F_997e4 | reflexivity | exact D_997e4
          | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
      step_simpl; vnorm.
      (* [comment removed for export] *)
      stepb_ft F_997e8 D_997e8 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepn F_997ec D_997ec.
      (* [comment removed for export] *)
      stepb_ft F_997f0 D_997f0 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
      (* [comment removed for export] *)
      stepb_tk F_997f4 D_997f4 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepn F_99818 D_99818. rewrite Ha0.
      (* [comment removed for export] *)
      stepn F_9981c D_9981c.
      (* [comment removed for export] *)
      stepn F_99510 D_99510. sp_renorm.
      stepST F_99514 D_99514 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x9ae54) ltac:(sok_stack SOK).
      stepST F_99518 D_99518 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
      stepST F_9951c D_9951c (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
      stepST F_99520 D_99520 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
      stepST F_99524 D_99524 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
      stepn F_99528 D_99528. stepn F_9952c D_9952c. stepn F_99530 D_99530. stepn F_99534 D_99534.
      (* [comment removed for export] *)
      stepn F_99538 D_99538.
      stepn F_aaadc D_aaadc.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_aaae0 | reflexivity | exact D_aaae0 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_aaae4 D_aaae4 ltac:(cond_compute).
      stepret F_aacd4 D_aacd4 (0x9ab70 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepLD F_9953c D_9953c (word_to_le_bytes 8 (Z_to_bv 64 0xea020)) (Z_to_bv 64 0xea020) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_99540 D_99540 ltac:(cond_compute).
      stepLD F_99544 D_99544 (word_to_le_bytes 4 (Z_to_bv 64 3)) (Z_to_bv 64 3) ltac:(addr_norm; rdn_by Msl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_99548 D_99548.
      stepn F_99560 D_99560.
      (* [comment removed for export] *)
      stepST F_99564 D_99564 (Z_to_bv 64 0xea010) (Z_to_bv 64 2) ltac:(sok_data).
      stepb_ft F_99568 D_99568 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepLD F_9956c D_9956c (word_to_le_bytes 8 (Z_to_bv 64 0xea020)) (Z_to_bv 64 0xea020) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_99570 D_99570.
      stepn F_99574 D_99574.
      stepLD F_99578 D_99578 (word_to_le_bytes 8 (Z_to_bv 64 0x58430)) (Z_to_bv 64 0x58430) ltac:(addr_norm; rdn_by Mf2) ltac:(apply bytes_le_to_Z_8).
      stepLD F_9957c D_9957c (word_to_le_bytes 8 (Z_to_bv 64 0xc85a8)) (Z_to_bv 64 0xc85a8) ltac:(addr_norm; rdn_by Ma2) ltac:(apply bytes_le_to_Z_8).
      (* [comment removed for export] *)
      stepn F_99580 D_99580.
      stepn F_99584 D_99584.
      stepLD F_aad64 D_aad64 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_aad68 D_aad68 ltac:(cond_compute).
      stepret F_aad6c D_aad6c (0x9abbc : word) ltac:(bveq).
      stepn F_99588 D_99588.
      stepret F_9958c D_9958c (0x58430 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepLBU F_56df0 D_56df0 (Z_to_bv 8 6) ltac:(addr_norm; rdn_by Msnan).
      stepn F_56df4 D_56df4.
      stepb_ft F_56df8 D_56df8 ltac:(cond_compute).
      stepret F_56dfc D_56dfc (0x9abc4 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepn F_99590 D_99590.
      stepn F_99594 D_99594.
      stepn F_aaadc D_aaadc.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_aaae0 | reflexivity | exact D_aaae0 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_aaae4 D_aaae4 ltac:(cond_compute).
      stepret F_aacd4 D_aacd4 (0x9abcc : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepLD F_99598 D_99598 (word_to_le_bytes 4 (Z_to_bv 64 2)) (Z_to_bv 64 2)
        ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9959c D_9959c.
      stepST F_995a0 D_995a0 (Z_to_bv 64 0xea010) (Z_to_bv 64 1) ltac:(sok_data).
      stepb_tk F_995a4 D_995a4 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepLD F_9956c D_9956c (word_to_le_bytes 8 (Z_to_bv 64 0xea020)) (Z_to_bv 64 0xea020) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_99570 D_99570.
      stepn F_99574 D_99574.
      stepLD F_99578 D_99578 (word_to_le_bytes 8 (Z_to_bv 64 0x58430)) (Z_to_bv 64 0x58430) ltac:(addr_norm; rdn_by Mf1) ltac:(apply bytes_le_to_Z_8).
      stepLD F_9957c D_9957c (word_to_le_bytes 8 (Z_to_bv 64 0xc8588)) (Z_to_bv 64 0xc8588) ltac:(addr_norm; rdn_by Ma1) ltac:(apply bytes_le_to_Z_8).
      (* [comment removed for export] *)
      stepn F_99580 D_99580.
      stepn F_99584 D_99584.
      stepLD F_aad64 D_aad64 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_aad68 D_aad68 ltac:(cond_compute).
      stepret F_aad6c D_aad6c (0x9abbc : word) ltac:(bveq).
      stepn F_99588 D_99588.
      stepret F_9958c D_9958c (0x58430 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepLBU F_56df0 D_56df0 (Z_to_bv 8 16) ltac:(addr_norm; rdn_by Msinf).
      stepn F_56df4 D_56df4.
      stepb_ft F_56df8 D_56df8 ltac:(cond_compute).
      stepret F_56dfc D_56dfc (0x9abc4 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepn F_99590 D_99590.
      stepn F_99594 D_99594.
      stepn F_aaadc D_aaadc.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_aaae0 | reflexivity | exact D_aaae0 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_aaae4 D_aaae4 ltac:(cond_compute).
      stepret F_aacd4 D_aacd4 (0x9abcc : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepLD F_99598 D_99598 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1)
        ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9959c D_9959c.
      stepST F_995a0 D_995a0 (Z_to_bv 64 0xea010) (Z_to_bv 64 0) ltac:(sok_data).
      stepb_tk F_995a4 D_995a4 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepLD F_9956c D_9956c (word_to_le_bytes 8 (Z_to_bv 64 0xea020)) (Z_to_bv 64 0xea020) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_99570 D_99570.
      stepn F_99574 D_99574.
      stepLD F_99578 D_99578 (word_to_le_bytes 8 (Z_to_bv 64 0x9ad9c)) (Z_to_bv 64 0x9ad9c) ltac:(addr_norm; rdn_by Mf0) ltac:(apply bytes_le_to_Z_8).
      stepLD F_9957c D_9957c (word_to_le_bytes 8 (Z_to_bv 64 0x346a4)) (Z_to_bv 64 0x346a4) ltac:(addr_norm; rdn_by Ma0) ltac:(apply bytes_le_to_Z_8).
      (* [comment removed for export] *)
      stepn F_99580 D_99580.
      stepn F_99584 D_99584.
      stepLD F_aad64 D_aad64 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_aad68 D_aad68 ltac:(cond_compute).
      stepret F_aad6c D_aad6c (0x9abbc : word) ltac:(bveq).
      stepn F_99588 D_99588.
      stepret F_9958c D_9958c (0x9ad9c : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepret F_99768 D_99768 (0x346a4 : word) ltac:(bveq).
      stepn F_34324 D_34324.
      stepLBU F_34328 D_34328 (Z_to_bv 8 0) ltac:(addr_norm; rdn_by Mcb).
      stepb_ft F_3432c D_3432c ltac:(cond_compute).
      stepret F_34330 D_34330 (0x9abc4 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepn F_99590 D_99590.
      stepn F_99594 D_99594.
      stepn F_aaadc D_aaadc.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_aaae0 | reflexivity | exact D_aaae0 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_aaae4 D_aaae4 ltac:(cond_compute).
      stepret F_aacd4 D_aacd4 (0x9abcc : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepLD F_99598 D_99598 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9959c D_9959c.
      stepST F_995a0 D_995a0 (Z_to_bv 64 0xea010) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
      stepb_ft F_995a4 D_995a4 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepLD F_995a8 D_995a8 (word_to_le_bytes 8 (Z_to_bv 64 0xea020)) (Z_to_bv 64 0xea020) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_995ac D_995ac.
      stepLD F_9954c D_9954c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mnx) ltac:(apply bytes_le_to_Z_8).
      stepn F_99550 D_99550.
      stepST F_99554 D_99554 (Z_to_bv 64 0xea010) (Z_to_bv 64 32) ltac:(sok_data).
      stepST F_99558 D_99558 (Z_to_bv 64 0xea018) (Z_to_bv 64 0) ltac:(sok_data).
      stepb_tk F_9955c D_9955c ltac:(cond_compute).
      stepn F_995b0 D_995b0.
      stepST F_995b4 D_995b4 (Z_to_bv 64 0xea008) (Z_to_bv 64 1) ltac:(sok_data).
      change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
      stepn F_995b8 D_995b8.
      stepLD8 F_995bc D_995bc (Z_to_bv 64 0x9ae54).
      stepLD8 F_995c0 D_995c0 code.
      stepLD8 F_995c4 D_995c4 (getr regs 9).
      stepLD8 F_995c8 D_995c8 (getr regs 18).
      stepLD8 F_995cc D_995cc (getr regs 19).
      stepn F_995d0 D_995d0. sp_renorm.
      (* [comment removed for export] *)
      stepn F_995d4 D_995d4.
      stepLD F_aad64 D_aad64 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_aad68 D_aad68 ltac:(cond_compute).
      stepret F_aad6c D_aad6c (0x9ae54 : word) ltac:(bveq).
      stepn F_99820 D_99820.
      apply mst_refl.
    - repeat split; gres; try reflexivity. exact Htp. }
  { (* [comment removed for export] *)
    destruct AX as (Mxl & Mxh & Msl & Mnx & Mf0 & Ma0 & Mf1 & Ma1 & Mf2 & Ma2 & Mf3 & Ma3 & Msinf & Msnan). unfold mem_w1, ax_writes. eexists. split.
    - (* [comment removed for export] *)
      stepn F_997bc D_997bc. rewrite Hsp. sp_renorm.
      (* [comment removed for export] *)
      stepST F_997c0 D_997c0 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
      stepST F_997c4 D_997c4 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
      (* [comment removed for export] *)
      stepn F_997c8 D_997c8.
      stepn F_997cc D_997cc. rewrite Htp.
      (* [comment removed for export] *)
      stepLD F_997d0 D_997d0 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
        ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      rewrite (v_lw_small tid) by lia.
      (* [comment removed for export] *)
      stepn F_997d4 D_997d4.
      stepn F_997d8 D_997d8.
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity
        | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
          [ exact F_997dc | reflexivity | exact D_997dc
          | gres; u_norm; reflexivity
          | gres; rdn_by Mlock
          | apply bytes_le_to_Z_4; u_norm; lia ]
        | ].
      reduce_bv_eqb_ifs; norm_pc_r; vnorm.
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity
        | eapply step_bne_ft_r; [exact F_997e0 | reflexivity | exact D_997e0 | gres; cond_compute ] | ].
      norm_pc_r.
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity
        | eapply step_sc_w_ok; [exact F_997e4 | reflexivity | exact D_997e4
          | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
      step_simpl; vnorm.
      (* [comment removed for export] *)
      stepb_ft F_997e8 D_997e8 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepn F_997ec D_997ec.
      (* [comment removed for export] *)
      stepb_ft F_997f0 D_997f0 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
      (* [comment removed for export] *)
      stepb_tk F_997f4 D_997f4 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepn F_99818 D_99818. rewrite Ha0.
      (* [comment removed for export] *)
      stepn F_9981c D_9981c.
      (* [comment removed for export] *)
      stepn F_99510 D_99510. sp_renorm.
      stepST F_99514 D_99514 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x9ae54) ltac:(sok_stack SOK).
      stepST F_99518 D_99518 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
      stepST F_9951c D_9951c (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
      stepST F_99520 D_99520 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
      stepST F_99524 D_99524 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
      stepn F_99528 D_99528. stepn F_9952c D_9952c. stepn F_99530 D_99530. stepn F_99534 D_99534.
      (* [comment removed for export] *)
      stepn F_99538 D_99538.
      stepn F_aaadc D_aaadc.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_aaae0 | reflexivity | exact D_aaae0 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_aaae4 D_aaae4 ltac:(cond_compute).
      stepret F_aacd4 D_aacd4 (0x9ab70 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepLD F_9953c D_9953c (word_to_le_bytes 8 (Z_to_bv 64 0xea020)) (Z_to_bv 64 0xea020) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_99540 D_99540 ltac:(cond_compute).
      stepLD F_99544 D_99544 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(addr_norm; rdn_by Msl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_99548 D_99548.
      stepn F_99560 D_99560.
      (* [comment removed for export] *)
      stepST F_99564 D_99564 (Z_to_bv 64 0xea010) (Z_to_bv 64 3) ltac:(sok_data).
      stepb_ft F_99568 D_99568 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepLD F_9956c D_9956c (word_to_le_bytes 8 (Z_to_bv 64 0xea020)) (Z_to_bv 64 0xea020) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_99570 D_99570.
      stepn F_99574 D_99574.
      stepLD F_99578 D_99578 (word_to_le_bytes 8 (Z_to_bv 64 0x58430)) (Z_to_bv 64 0x58430) ltac:(addr_norm; rdn_by Mf3) ltac:(apply bytes_le_to_Z_8).
      stepLD F_9957c D_9957c (word_to_le_bytes 8 (Z_to_bv 64 0xc85a8)) (Z_to_bv 64 0xc85a8) ltac:(addr_norm; rdn_by Ma3) ltac:(apply bytes_le_to_Z_8).
      (* [comment removed for export] *)
      stepn F_99580 D_99580.
      stepn F_99584 D_99584.
      stepLD F_aad64 D_aad64 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_aad68 D_aad68 ltac:(cond_compute).
      stepret F_aad6c D_aad6c (0x9abbc : word) ltac:(bveq).
      stepn F_99588 D_99588.
      stepret F_9958c D_9958c (0x58430 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepLBU F_56df0 D_56df0 (Z_to_bv 8 6) ltac:(addr_norm; rdn_by Msnan).
      stepn F_56df4 D_56df4.
      stepb_ft F_56df8 D_56df8 ltac:(cond_compute).
      stepret F_56dfc D_56dfc (0x9abc4 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepn F_99590 D_99590.
      stepn F_99594 D_99594.
      stepn F_aaadc D_aaadc.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_aaae0 | reflexivity | exact D_aaae0 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_aaae4 D_aaae4 ltac:(cond_compute).
      stepret F_aacd4 D_aacd4 (0x9abcc : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepLD F_99598 D_99598 (word_to_le_bytes 4 (Z_to_bv 64 3)) (Z_to_bv 64 3)
        ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9959c D_9959c.
      stepST F_995a0 D_995a0 (Z_to_bv 64 0xea010) (Z_to_bv 64 2) ltac:(sok_data).
      stepb_tk F_995a4 D_995a4 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepLD F_9956c D_9956c (word_to_le_bytes 8 (Z_to_bv 64 0xea020)) (Z_to_bv 64 0xea020) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_99570 D_99570.
      stepn F_99574 D_99574.
      stepLD F_99578 D_99578 (word_to_le_bytes 8 (Z_to_bv 64 0x58430)) (Z_to_bv 64 0x58430) ltac:(addr_norm; rdn_by Mf2) ltac:(apply bytes_le_to_Z_8).
      stepLD F_9957c D_9957c (word_to_le_bytes 8 (Z_to_bv 64 0xc8588)) (Z_to_bv 64 0xc8588) ltac:(addr_norm; rdn_by Ma2) ltac:(apply bytes_le_to_Z_8).
      (* [comment removed for export] *)
      stepn F_99580 D_99580.
      stepn F_99584 D_99584.
      stepLD F_aad64 D_aad64 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_aad68 D_aad68 ltac:(cond_compute).
      stepret F_aad6c D_aad6c (0x9abbc : word) ltac:(bveq).
      stepn F_99588 D_99588.
      stepret F_9958c D_9958c (0x58430 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepLBU F_56df0 D_56df0 (Z_to_bv 8 16) ltac:(addr_norm; rdn_by Msinf).
      stepn F_56df4 D_56df4.
      stepb_ft F_56df8 D_56df8 ltac:(cond_compute).
      stepret F_56dfc D_56dfc (0x9abc4 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepn F_99590 D_99590.
      stepn F_99594 D_99594.
      stepn F_aaadc D_aaadc.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_aaae0 | reflexivity | exact D_aaae0 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_aaae4 D_aaae4 ltac:(cond_compute).
      stepret F_aacd4 D_aacd4 (0x9abcc : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepLD F_99598 D_99598 (word_to_le_bytes 4 (Z_to_bv 64 2)) (Z_to_bv 64 2)
        ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9959c D_9959c.
      stepST F_995a0 D_995a0 (Z_to_bv 64 0xea010) (Z_to_bv 64 1) ltac:(sok_data).
      stepb_tk F_995a4 D_995a4 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepLD F_9956c D_9956c (word_to_le_bytes 8 (Z_to_bv 64 0xea020)) (Z_to_bv 64 0xea020) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_99570 D_99570.
      stepn F_99574 D_99574.
      stepLD F_99578 D_99578 (word_to_le_bytes 8 (Z_to_bv 64 0x57e98)) (Z_to_bv 64 0x57e98) ltac:(addr_norm; rdn_by Mf1) ltac:(apply bytes_le_to_Z_8).
      stepLD F_9957c D_9957c (word_to_le_bytes 8 (Z_to_bv 64 0xb8240)) (Z_to_bv 64 0xb8240) ltac:(addr_norm; rdn_by Ma1) ltac:(apply bytes_le_to_Z_8).
      (* [comment removed for export] *)
      stepn F_99580 D_99580.
      stepn F_99584 D_99584.
      stepLD F_aad64 D_aad64 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_aad68 D_aad68 ltac:(cond_compute).
      stepret F_aad6c D_aad6c (0x9abbc : word) ltac:(bveq).
      stepn F_99588 D_99588.
      stepret F_9958c D_9958c (0x57e98 : word) ltac:(bveq).
      stepret F_56858 D_56858 (0x9abc4 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepn F_99590 D_99590.
      stepn F_99594 D_99594.
      stepn F_aaadc D_aaadc.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_aaae0 | reflexivity | exact D_aaae0 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_aaae4 D_aaae4 ltac:(cond_compute).
      stepret F_aacd4 D_aacd4 (0x9abcc : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepLD F_99598 D_99598 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1)
        ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9959c D_9959c.
      stepST F_995a0 D_995a0 (Z_to_bv 64 0xea010) (Z_to_bv 64 0) ltac:(sok_data).
      stepb_tk F_995a4 D_995a4 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepLD F_9956c D_9956c (word_to_le_bytes 8 (Z_to_bv 64 0xea020)) (Z_to_bv 64 0xea020) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_99570 D_99570.
      stepn F_99574 D_99574.
      stepLD F_99578 D_99578 (word_to_le_bytes 8 (Z_to_bv 64 0x9ad9c)) (Z_to_bv 64 0x9ad9c) ltac:(addr_norm; rdn_by Mf0) ltac:(apply bytes_le_to_Z_8).
      stepLD F_9957c D_9957c (word_to_le_bytes 8 (Z_to_bv 64 0x346a4)) (Z_to_bv 64 0x346a4) ltac:(addr_norm; rdn_by Ma0) ltac:(apply bytes_le_to_Z_8).
      (* [comment removed for export] *)
      stepn F_99580 D_99580.
      stepn F_99584 D_99584.
      stepLD F_aad64 D_aad64 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_aad68 D_aad68 ltac:(cond_compute).
      stepret F_aad6c D_aad6c (0x9abbc : word) ltac:(bveq).
      stepn F_99588 D_99588.
      stepret F_9958c D_9958c (0x9ad9c : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepret F_99768 D_99768 (0x346a4 : word) ltac:(bveq).
      stepn F_34324 D_34324.
      stepLBU F_34328 D_34328 (Z_to_bv 8 0) ltac:(addr_norm; rdn_by Mcb).
      stepb_ft F_3432c D_3432c ltac:(cond_compute).
      stepret F_34330 D_34330 (0x9abc4 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepn F_99590 D_99590.
      stepn F_99594 D_99594.
      stepn F_aaadc D_aaadc.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_aaae0 | reflexivity | exact D_aaae0 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_aaae4 D_aaae4 ltac:(cond_compute).
      stepret F_aacd4 D_aacd4 (0x9abcc : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepLD F_99598 D_99598 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9959c D_9959c.
      stepST F_995a0 D_995a0 (Z_to_bv 64 0xea010) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
      stepb_ft F_995a4 D_995a4 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepLD F_995a8 D_995a8 (word_to_le_bytes 8 (Z_to_bv 64 0xea020)) (Z_to_bv 64 0xea020) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_995ac D_995ac.
      stepLD F_9954c D_9954c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mnx) ltac:(apply bytes_le_to_Z_8).
      stepn F_99550 D_99550.
      stepST F_99554 D_99554 (Z_to_bv 64 0xea010) (Z_to_bv 64 32) ltac:(sok_data).
      stepST F_99558 D_99558 (Z_to_bv 64 0xea018) (Z_to_bv 64 0) ltac:(sok_data).
      stepb_tk F_9955c D_9955c ltac:(cond_compute).
      stepn F_995b0 D_995b0.
      stepST F_995b4 D_995b4 (Z_to_bv 64 0xea008) (Z_to_bv 64 1) ltac:(sok_data).
      change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
      stepn F_995b8 D_995b8.
      stepLD8 F_995bc D_995bc (Z_to_bv 64 0x9ae54).
      stepLD8 F_995c0 D_995c0 code.
      stepLD8 F_995c4 D_995c4 (getr regs 9).
      stepLD8 F_995c8 D_995c8 (getr regs 18).
      stepLD8 F_995cc D_995cc (getr regs 19).
      stepn F_995d0 D_995d0. sp_renorm.
      (* [comment removed for export] *)
      stepn F_995d4 D_995d4.
      stepLD F_aad64 D_aad64 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_aad68 D_aad68 ltac:(cond_compute).
      stepret F_aad6c D_aad6c (0x9ae54 : word) ltac:(bveq).
      stepn F_99820 D_99820.
      apply mst_refl.
    - repeat split; gres; try reflexivity. exact Htp. }
  { (* [comment removed for export] *)
    destruct AX as (Mxl & Mxh & Msl & Mnx & Mf0 & Ma0 & Mf1 & Ma1 & Mf2 & Ma2 & Mf3 & Ma3 & Msinf & Msnan). unfold mem_w1, ax_writes. eexists. split.
    - (* [comment removed for export] *)
      stepn F_997bc D_997bc. rewrite Hsp. sp_renorm.
      (* [comment removed for export] *)
      stepST F_997c0 D_997c0 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
      stepST F_997c4 D_997c4 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
      (* [comment removed for export] *)
      stepn F_997c8 D_997c8.
      stepn F_997cc D_997cc. rewrite Htp.
      (* [comment removed for export] *)
      stepLD F_997d0 D_997d0 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
        ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      rewrite (v_lw_small tid) by lia.
      (* [comment removed for export] *)
      stepn F_997d4 D_997d4.
      stepn F_997d8 D_997d8.
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity
        | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
          [ exact F_997dc | reflexivity | exact D_997dc
          | gres; u_norm; reflexivity
          | gres; rdn_by Mlock
          | apply bytes_le_to_Z_4; u_norm; lia ]
        | ].
      reduce_bv_eqb_ifs; norm_pc_r; vnorm.
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity
        | eapply step_bne_ft_r; [exact F_997e0 | reflexivity | exact D_997e0 | gres; cond_compute ] | ].
      norm_pc_r.
      (* [comment removed for export] *)
      eapply mst_step; [reflexivity
        | eapply step_sc_w_ok; [exact F_997e4 | reflexivity | exact D_997e4
          | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
      step_simpl; vnorm.
      (* [comment removed for export] *)
      stepb_ft F_997e8 D_997e8 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepn F_997ec D_997ec.
      (* [comment removed for export] *)
      stepb_ft F_997f0 D_997f0 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
      (* [comment removed for export] *)
      stepb_tk F_997f4 D_997f4 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepn F_99818 D_99818. rewrite Ha0.
      (* [comment removed for export] *)
      stepn F_9981c D_9981c.
      (* [comment removed for export] *)
      stepn F_99510 D_99510. sp_renorm.
      stepST F_99514 D_99514 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x9ae54) ltac:(sok_stack SOK).
      stepST F_99518 D_99518 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
      stepST F_9951c D_9951c (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
      stepST F_99520 D_99520 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
      stepST F_99524 D_99524 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
      stepn F_99528 D_99528. stepn F_9952c D_9952c. stepn F_99530 D_99530. stepn F_99534 D_99534.
      (* [comment removed for export] *)
      stepn F_99538 D_99538.
      stepn F_aaadc D_aaadc.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_aaae0 | reflexivity | exact D_aaae0 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_aaae4 D_aaae4 ltac:(cond_compute).
      stepret F_aacd4 D_aacd4 (0x9ab70 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepLD F_9953c D_9953c (word_to_le_bytes 8 (Z_to_bv 64 0xea020)) (Z_to_bv 64 0xea020) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepb_ft F_99540 D_99540 ltac:(cond_compute).
      stepLD F_99544 D_99544 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(addr_norm; rdn_by Msl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_99548 D_99548.
      stepn F_99560 D_99560.
      (* [comment removed for export] *)
      stepST F_99564 D_99564 (Z_to_bv 64 0xea010) (Z_to_bv 64 3) ltac:(sok_data).
      stepb_ft F_99568 D_99568 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepLD F_9956c D_9956c (word_to_le_bytes 8 (Z_to_bv 64 0xea020)) (Z_to_bv 64 0xea020) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_99570 D_99570.
      stepn F_99574 D_99574.
      stepLD F_99578 D_99578 (word_to_le_bytes 8 (Z_to_bv 64 0x57e98)) (Z_to_bv 64 0x57e98) ltac:(addr_norm; rdn_by Mf3) ltac:(apply bytes_le_to_Z_8).
      stepLD F_9957c D_9957c (word_to_le_bytes 8 (Z_to_bv 64 0xb8240)) (Z_to_bv 64 0xb8240) ltac:(addr_norm; rdn_by Ma3) ltac:(apply bytes_le_to_Z_8).
      (* [comment removed for export] *)
      stepn F_99580 D_99580.
      stepn F_99584 D_99584.
      stepLD F_aad64 D_aad64 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_aad68 D_aad68 ltac:(cond_compute).
      stepret F_aad6c D_aad6c (0x9abbc : word) ltac:(bveq).
      stepn F_99588 D_99588.
      stepret F_9958c D_9958c (0x57e98 : word) ltac:(bveq).
      stepret F_56858 D_56858 (0x9abc4 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepn F_99590 D_99590.
      stepn F_99594 D_99594.
      stepn F_aaadc D_aaadc.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_aaae0 | reflexivity | exact D_aaae0 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_aaae4 D_aaae4 ltac:(cond_compute).
      stepret F_aacd4 D_aacd4 (0x9abcc : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepLD F_99598 D_99598 (word_to_le_bytes 4 (Z_to_bv 64 3)) (Z_to_bv 64 3)
        ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9959c D_9959c.
      stepST F_995a0 D_995a0 (Z_to_bv 64 0xea010) (Z_to_bv 64 2) ltac:(sok_data).
      stepb_tk F_995a4 D_995a4 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepLD F_9956c D_9956c (word_to_le_bytes 8 (Z_to_bv 64 0xea020)) (Z_to_bv 64 0xea020) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_99570 D_99570.
      stepn F_99574 D_99574.
      stepLD F_99578 D_99578 (word_to_le_bytes 8 (Z_to_bv 64 0x58430)) (Z_to_bv 64 0x58430) ltac:(addr_norm; rdn_by Mf2) ltac:(apply bytes_le_to_Z_8).
      stepLD F_9957c D_9957c (word_to_le_bytes 8 (Z_to_bv 64 0xc85a8)) (Z_to_bv 64 0xc85a8) ltac:(addr_norm; rdn_by Ma2) ltac:(apply bytes_le_to_Z_8).
      (* [comment removed for export] *)
      stepn F_99580 D_99580.
      stepn F_99584 D_99584.
      stepLD F_aad64 D_aad64 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_aad68 D_aad68 ltac:(cond_compute).
      stepret F_aad6c D_aad6c (0x9abbc : word) ltac:(bveq).
      stepn F_99588 D_99588.
      stepret F_9958c D_9958c (0x58430 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepLBU F_56df0 D_56df0 (Z_to_bv 8 6) ltac:(addr_norm; rdn_by Msnan).
      stepn F_56df4 D_56df4.
      stepb_ft F_56df8 D_56df8 ltac:(cond_compute).
      stepret F_56dfc D_56dfc (0x9abc4 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepn F_99590 D_99590.
      stepn F_99594 D_99594.
      stepn F_aaadc D_aaadc.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_aaae0 | reflexivity | exact D_aaae0 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_aaae4 D_aaae4 ltac:(cond_compute).
      stepret F_aacd4 D_aacd4 (0x9abcc : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepLD F_99598 D_99598 (word_to_le_bytes 4 (Z_to_bv 64 2)) (Z_to_bv 64 2)
        ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9959c D_9959c.
      stepST F_995a0 D_995a0 (Z_to_bv 64 0xea010) (Z_to_bv 64 1) ltac:(sok_data).
      stepb_tk F_995a4 D_995a4 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepLD F_9956c D_9956c (word_to_le_bytes 8 (Z_to_bv 64 0xea020)) (Z_to_bv 64 0xea020) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_99570 D_99570.
      stepn F_99574 D_99574.
      stepLD F_99578 D_99578 (word_to_le_bytes 8 (Z_to_bv 64 0x58430)) (Z_to_bv 64 0x58430) ltac:(addr_norm; rdn_by Mf1) ltac:(apply bytes_le_to_Z_8).
      stepLD F_9957c D_9957c (word_to_le_bytes 8 (Z_to_bv 64 0xc8588)) (Z_to_bv 64 0xc8588) ltac:(addr_norm; rdn_by Ma1) ltac:(apply bytes_le_to_Z_8).
      (* [comment removed for export] *)
      stepn F_99580 D_99580.
      stepn F_99584 D_99584.
      stepLD F_aad64 D_aad64 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_aad68 D_aad68 ltac:(cond_compute).
      stepret F_aad6c D_aad6c (0x9abbc : word) ltac:(bveq).
      stepn F_99588 D_99588.
      stepret F_9958c D_9958c (0x58430 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepLBU F_56df0 D_56df0 (Z_to_bv 8 16) ltac:(addr_norm; rdn_by Msinf).
      stepn F_56df4 D_56df4.
      stepb_ft F_56df8 D_56df8 ltac:(cond_compute).
      stepret F_56dfc D_56dfc (0x9abc4 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepn F_99590 D_99590.
      stepn F_99594 D_99594.
      stepn F_aaadc D_aaadc.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_aaae0 | reflexivity | exact D_aaae0 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_aaae4 D_aaae4 ltac:(cond_compute).
      stepret F_aacd4 D_aacd4 (0x9abcc : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepLD F_99598 D_99598 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1)
        ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9959c D_9959c.
      stepST F_995a0 D_995a0 (Z_to_bv 64 0xea010) (Z_to_bv 64 0) ltac:(sok_data).
      stepb_tk F_995a4 D_995a4 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepLD F_9956c D_9956c (word_to_le_bytes 8 (Z_to_bv 64 0xea020)) (Z_to_bv 64 0xea020) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_99570 D_99570.
      stepn F_99574 D_99574.
      stepLD F_99578 D_99578 (word_to_le_bytes 8 (Z_to_bv 64 0x9ad9c)) (Z_to_bv 64 0x9ad9c) ltac:(addr_norm; rdn_by Mf0) ltac:(apply bytes_le_to_Z_8).
      stepLD F_9957c D_9957c (word_to_le_bytes 8 (Z_to_bv 64 0x346a4)) (Z_to_bv 64 0x346a4) ltac:(addr_norm; rdn_by Ma0) ltac:(apply bytes_le_to_Z_8).
      (* [comment removed for export] *)
      stepn F_99580 D_99580.
      stepn F_99584 D_99584.
      stepLD F_aad64 D_aad64 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_aad68 D_aad68 ltac:(cond_compute).
      stepret F_aad6c D_aad6c (0x9abbc : word) ltac:(bveq).
      stepn F_99588 D_99588.
      stepret F_9958c D_9958c (0x9ad9c : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepret F_99768 D_99768 (0x346a4 : word) ltac:(bveq).
      stepn F_34324 D_34324.
      stepLBU F_34328 D_34328 (Z_to_bv 8 0) ltac:(addr_norm; rdn_by Mcb).
      stepb_ft F_3432c D_3432c ltac:(cond_compute).
      stepret F_34330 D_34330 (0x9abc4 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepn F_99590 D_99590.
      stepn F_99594 D_99594.
      stepn F_aaadc D_aaadc.
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 0);
          [exact F_aaae0 | reflexivity | exact D_aaae0 | gres; imm_norm; addr_norm; rdn_by Gnl]
        | step_simpl]; vnorm.
      stepb_tk F_aaae4 D_aaae4 ltac:(cond_compute).
      stepret F_aacd4 D_aacd4 (0x9abcc : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepLD F_99598 D_99598 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(addr_norm; lazymatch goal with |- rdn ?s (wbytes ?m ?a ?bs) _ _ = _ => pose proof (rdn_wbytes_hit s bs m a) as HH; rewrite length_N_to_le_bytes in HH; apply HH; zsimp; lia end)
        ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_9959c D_9959c.
      stepST F_995a0 D_995a0 (Z_to_bv 64 0xea010) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
      stepb_ft F_995a4 D_995a4 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepLD F_995a8 D_995a8 (word_to_le_bytes 8 (Z_to_bv 64 0xea020)) (Z_to_bv 64 0xea020) ltac:(addr_norm; rdn_by Mxh) ltac:(apply bytes_le_to_Z_8).
      stepn F_995ac D_995ac.
      stepLD F_9954c D_9954c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mnx) ltac:(apply bytes_le_to_Z_8).
      stepn F_99550 D_99550.
      stepST F_99554 D_99554 (Z_to_bv 64 0xea010) (Z_to_bv 64 32) ltac:(sok_data).
      stepST F_99558 D_99558 (Z_to_bv 64 0xea018) (Z_to_bv 64 0) ltac:(sok_data).
      stepb_tk F_9955c D_9955c ltac:(cond_compute).
      stepn F_995b0 D_995b0.
      stepST F_995b4 D_995b4 (Z_to_bv 64 0xea008) (Z_to_bv 64 1) ltac:(sok_data).
      change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
      stepn F_995b8 D_995b8.
      stepLD8 F_995bc D_995bc (Z_to_bv 64 0x9ae54).
      stepLD8 F_995c0 D_995c0 code.
      stepLD8 F_995c4 D_995c4 (getr regs 9).
      stepLD8 F_995c8 D_995c8 (getr regs 18).
      stepLD8 F_995cc D_995cc (getr regs 19).
      stepn F_995d0 D_995d0. sp_renorm.
      (* [comment removed for export] *)
      stepn F_995d4 D_995d4.
      stepLD F_aad64 D_aad64 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_by Mxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepb_ft F_aad68 D_aad68 ltac:(cond_compute).
      stepret F_aad6c D_aad6c (0x9ae54 : word) ltac:(bveq).
      stepn F_99820 D_99820.
      apply mst_refl.
    - repeat split; gres; try reflexivity. exact Htp. }
Qed.

(* [comment removed for export] *)
Definition mem_w2 (mem : word -> option byte) (sp code s1v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x9ae58)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x9add4)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0xb14f0)))
    (Z_to_bv 64 0xb8548) [Z_to_bv 8 1].

Lemma w2 : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x9ae58 -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0xb71f0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb14f8)) ->
  rdn RSEGS mem (Z_to_bv 64 0xb71f8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb14f0)) ->
  rdn RSEGS mem (Z_to_bv 64 0xb14f0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x341ec)) ->
  rdn RSEGS mem (Z_to_bv 64 0xb8548) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0xb7080) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x9ac0c)) ->
  rdn RSEGS mem (Z_to_bv 64 0xb8218) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb8218)) ->
  rdn RSEGS mem (Z_to_bv 64 0xb7088) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x9ada4 : word) mem rom)
                 (mkst regs' (0xa03f8 : word) (mem_w2 mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x9ae5c
    /\ getr regs' 9 = s1v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hra Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mdso Mg2.
  unfold mem_w2. eexists. split.
  - (* [comment removed for export] *)
    stepn F_99770 D_99770. rewrite Hsp. sp_renorm.
    stepST F_99774 D_99774 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x9ae58) ltac:(sok_stack SOK).
    stepST F_99778 D_99778 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_9977c D_9977c (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_99780 D_99780.
    stepn F_99784 D_99784.
    stepLD8 F_99788 D_99788 (Z_to_bv 64 0xb14f8).
    stepLD8 F_9978c D_9978c (Z_to_bv 64 0xb14f0).
    (* [comment removed for export] *)
    stepb_ft F_99790 D_99790 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_99794 D_99794 (Z_to_bv 64 0x341ec).
    stepn F_99798 D_99798.
    stepjr F_9979c D_9979c (Z_to_bv 64 0x341ec) ltac:(gres; reflexivity). vnorm.
    (* [comment removed for export] *)
    stepn F_33e6c D_33e6c. sp_renorm.
    stepST F_33e70 D_33e70 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x9add4) ltac:(sok_stack SOK).
    stepST F_33e74 D_33e74 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0xb14f0) ltac:(sok_stack SOK).
    stepn F_33e78 D_33e78.
    stepn F_33e7c D_33e7c.
    stepn F_33e80 D_33e80.
    (* [comment removed for export] *)
    stepLBU F_33e84 D_33e84 (Z_to_bv 8 0) ltac:(rewrite v_addi_0; rdn_by Mcomp).
    stepn F_33e88 D_33e88.
    stepb_tk F_33e8c D_33e8c ltac:(cond_compute).
    stepn F_33e98 D_33e98.
    stepn F_33e9c D_33e9c.
    stepn F_33ea0 D_33ea0.
    (* [comment removed for export] *)
    stepST F_33ea4 D_33ea4 (Z_to_bv 64 0xb8548) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_33ea8 D_33ea8.
    stepLD8 F_33eac D_33eac (Z_to_bv 64 0x9ac0c).
    (* [comment removed for export] *)
    stepb_ft F_33eb0 D_33eb0 ltac:(cond_compute).
    stepn F_33eb4 D_33eb4.
    stepn F_33eb8 D_33eb8.
    stepn F_33ebc D_33ebc.
    stepLD8 F_33ec0 D_33ec0 (Z_to_bv 64 0xb8218).
    stepn F_33ec4 D_33ec4.
    stepret F_995d8 D_995d8 (0x34248 : word) ltac:(bveq).
    stepn F_33ec8 D_33ec8.
    (* [comment removed for export] *)
    stepn F_33ecc D_33ecc.
    stepLD8 F_33ed0 D_33ed0 (Z_to_bv 64 0).
    stepb_tk F_33ed4 D_33ed4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_33eec D_33eec (Z_to_bv 64 0x9add4).
    stepLD8 F_33ef0 D_33ef0 (Z_to_bv 64 0xb14f0).
    stepn F_33ef4 D_33ef4. sp_renorm.
    stepret F_33ef8 D_33ef8 (0x9add4 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_997a0 D_997a0.
    stepb_ft F_997a4 D_997a4 ltac:(cond_compute).
    stepLD8 F_997a8 D_997a8 (Z_to_bv 64 0x9ae58).
    stepLD8 F_997ac D_997ac code.
    stepLD8 F_997b0 D_997b0 s1v.
    stepn F_997b4 D_997b4. sp_renorm.
    (* [comment removed for export] *)
    stepn F_997b8 D_997b8.
    stepret F_9976c D_9976c (0x9ae58 : word) ltac:(bveq).
    stepn F_99824 D_99824.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End FPX_1.


(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
