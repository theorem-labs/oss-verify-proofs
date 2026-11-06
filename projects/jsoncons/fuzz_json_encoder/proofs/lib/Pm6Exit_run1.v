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
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic
  Pm6ExitBase Pm6_code_3975c_3a000 Pm6_code_a9000_aa000          .
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.


(* [comment removed for export] *)
Definition mem_w1 (mem : word -> option byte) (sp ra s0 : word) (tid : Z) :=
  wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (bv_unsigned sp - 16)) (word_to_le_bytes 8 s0))
    (Z_to_bv 64 0xf9888) (word_to_le_bytes 4 (Z_to_bv 64 tid)).

Lemma w1 : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn RSEGS mem (Z_to_bv 64 0xf9888) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0xa9fc8 : word) mem rom)
                 (mkst regs' (0xa9d1c : word) (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0xaa02c
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock.
  unfold mem_w1. eexists. split.
  - (* [comment removed for export] *)
    stepn F_a9f8c D_a9f8c. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_a9f90 D_a9f90 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_a9f94 D_a9f94 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_a9f98 D_a9f98.
    stepn F_a9f9c D_a9f9c. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_a9fa0 D_a9fa0 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_a9fa4 D_a9fa4.
    stepn F_a9fa8 D_a9fa8.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_a9fac | reflexivity | exact D_a9fac
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_a9fb0 | reflexivity | exact D_a9fb0 | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_a9fb4 | reflexivity | exact D_a9fb4
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_a9fb8 D_a9fb8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_a9fbc D_a9fbc.
    (* [comment removed for export] *)
    stepb_ft F_a9fc0 D_a9fc0 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_a9fc4 D_a9fc4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_a9fe8 D_a9fe8. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_a9fec D_a9fec.
    apply mst_refl.
  - repeat split; gres; try reflexivity. exact Htp.
Qed.

(* [comment removed for export] *)
Lemma w1b : forall regs mem rom,
  exists regs',
    msteps RSEGS (mkst regs (0xaa02c : word) mem rom) (mkst regs' (0xa9f7c : word) mem rom)
    /\ getr regs' 1 = Z_to_bv 64 0xaa030
    /\ (forall r : reg, r <> 1%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom. eexists. split.
  - stepn F_a9ff0 D_a9ff0. apply mst_refl.
  - split; [gres; reflexivity|]. intros r Hr. apply getr_other. exact Hr.
Qed.

(* [comment removed for export] *)
Definition mem_w2 (mem : word -> option byte) (sp code s1v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0xaa030)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0xa9fac)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0xc06c8)))
    (Z_to_bv 64 0xc7b98) [Z_to_bv 8 1].

Lemma w2 : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0xaa030 -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0xc6838) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xc06d0)) ->
  rdn RSEGS mem (Z_to_bv 64 0xc6840) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xc06c8)) ->
  rdn RSEGS mem (Z_to_bv 64 0xc06c8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x39860)) ->
  rdn RSEGS mem (Z_to_bv 64 0xc7b98) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0xc66a0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xa9de4)) ->
  rdn RSEGS mem (Z_to_bv 64 0xc66a8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0xc7860) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xc7860)) ->
  exists regs',
    msteps RSEGS (mkst regs (0xa9f7c : word) mem rom)
                 (mkst regs' (0xaf66c : word) (mem_w2 mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0xaa034
    /\ getr regs' 9 = s1v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hra Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mg2 Mdso.
  unfold mem_w2. eexists. split.
  - (* [comment removed for export] *)
    stepn F_a9f40 D_a9f40. rewrite Hsp. sp_renorm.
    stepST F_a9f44 D_a9f44 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0xaa030) ltac:(sok_stack SOK).
    stepST F_a9f48 D_a9f48 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_a9f4c D_a9f4c (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_a9f50 D_a9f50.
    stepn F_a9f54 D_a9f54.
    stepLD8 F_a9f58 D_a9f58 (Z_to_bv 64 0xc06d0).
    stepLD8 F_a9f5c D_a9f5c (Z_to_bv 64 0xc06c8).
    (* [comment removed for export] *)
    stepb_ft F_a9f60 D_a9f60 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_a9f64 D_a9f64 (Z_to_bv 64 0x39860).
    stepn F_a9f68 D_a9f68.
    stepjr F_a9f6c D_a9f6c (Z_to_bv 64 0x39860) ltac:(gres; reflexivity). vnorm.
    (* [comment removed for export] *)
    stepn F_39818 D_39818. sp_renorm.
    stepST F_3981c D_3981c (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0xa9fac) ltac:(sok_stack SOK).
    stepST F_39820 D_39820 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0xc06c8) ltac:(sok_stack SOK).
    stepn F_39824 D_39824.
    stepn F_39828 D_39828.
    stepn F_3982c D_3982c.
    (* [comment removed for export] *)
    stepLBU F_39830 D_39830 (Z_to_bv 8 0) ltac:(rewrite v_addi_0; rdn_by Mcomp).
    stepn F_39834 D_39834.
    stepb_tk F_39838 D_39838 ltac:(cond_compute).
    stepn F_39844 D_39844.
    stepn F_39848 D_39848.
    stepn F_3984c D_3984c.
    (* [comment removed for export] *)
    stepST F_39850 D_39850 (Z_to_bv 64 0xc7b98) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_39854 D_39854.
    stepLD8 F_39858 D_39858 (Z_to_bv 64 0xa9de4).
    stepb_ft F_3985c D_3985c ltac:(cond_compute).
    stepn F_39860 D_39860.
    stepn F_39864 D_39864.
    stepn F_39868 D_39868.
    stepLD8 F_3986c D_3986c (Z_to_bv 64 0xc7860).
    stepn F_39870 D_39870.
    stepret F_a9da8 D_a9da8 (0x398bc : word) ltac:(bveq).
    stepn F_39874 D_39874.
    (* [comment removed for export] *)
    stepn F_39878 D_39878.
    stepLD8 F_3987c D_3987c (Z_to_bv 64 0).
    stepb_tk F_39880 D_39880 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_39898 D_39898 (Z_to_bv 64 0xa9fac).
    stepLD8 F_3989c D_3989c (Z_to_bv 64 0xc06c8).
    stepn F_398a0 D_398a0. sp_renorm.
    stepret F_398a4 D_398a4 (0xa9fac : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_a9f70 D_a9f70.
    stepb_ft F_a9f74 D_a9f74 ltac:(cond_compute).
    stepLD8 F_a9f78 D_a9f78 (Z_to_bv 64 0xaa030).
    stepLD8 F_a9f7c D_a9f7c code.
    stepLD8 F_a9f80 D_a9f80 s1v.
    stepn F_a9f84 D_a9f84. sp_renorm.
    (* [comment removed for export] *)
    stepn F_a9f88 D_a9f88.
    stepret F_a9f3c D_a9f3c (0xaa030 : word) ltac:(bveq).
    stepn F_a9ff4 D_a9ff4.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End FPX_1.


(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
