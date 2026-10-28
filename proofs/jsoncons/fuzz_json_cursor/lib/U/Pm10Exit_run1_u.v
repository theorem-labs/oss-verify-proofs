(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10ExitBase_u Pm10_code_38dc8_39000_u Pm10_code_a5000_a6000_u          .
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.

Definition mem_w1 (mem : word -> option byte) (sp ra s0 : word) (tid : Z) :=
  wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (bv_unsigned sp - 16)) (word_to_le_bytes 8 s0))
    (Z_to_bv 64 0xf6a68) (word_to_le_bytes 4 (Z_to_bv 64 tid)).

Lemma w1 : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn RSEGS mem (Z_to_bv 64 0xf6a68) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0xa7160 : word) mem rom)
                 (mkst regs' (0xa6eb4 : word) (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0xa71c4
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock.
  unfold mem_w1. eexists. split.
  -
    stepn F_a5370 D_a5370. rewrite Hsp. sp_renorm.

    stepST F_a5374 D_a5374 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_a5378 D_a5378 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).

    stepn F_a537c D_a537c.
    stepn F_a5380 D_a5380. rewrite Htp.

    stepLD F_a5384 D_a5384 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.

    stepn F_a5388 D_a5388.
    stepn F_a538c D_a538c.

    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_a5390 | reflexivity | exact D_a5390
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.

    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_a5394 | reflexivity | exact D_a5394 | gres; cond_compute ] | ].
    norm_pc_r.

    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_a5398 | reflexivity | exact D_a5398
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.

    stepb_ft F_a539c D_a539c ltac:(cond_compute).

    stepn F_a53a0 D_a53a0.

    stepb_ft F_a53a4 D_a53a4 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).

    stepb_tk F_a53a8 D_a53a8 ltac:(cond_compute).

    stepn F_a53cc D_a53cc. rewrite Ha0.

    stepn F_a53d0 D_a53d0.
    apply mst_refl.
  - repeat split; gres; try reflexivity. exact Htp.
Qed.

Lemma w1b : forall regs mem rom,
  exists regs',
    msteps RSEGS (mkst regs (0xa71c4 : word) mem rom) (mkst regs' (0xa7114 : word) mem rom)
    /\ getr regs' 1 = Z_to_bv 64 0xa71c8
    /\ (forall r : reg, r <> 1%bv -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom. eexists. split.
  - stepn F_a53d4 D_a53d4. apply mst_refl.
  - split; [gres; reflexivity|]. intros r Hr. apply getr_other. exact Hr.
Qed.

Definition mem_w2 (mem : word -> option byte) (sp code s1v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0xa71c8)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0xa7144)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0xbd900)))
    (Z_to_bv 64 0xc4db8) [Z_to_bv 8 1].

Lemma w2 : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0xa71c8 -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0xc3a50) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xbd908)) ->
  rdn RSEGS mem (Z_to_bv 64 0xc3a58) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xbd900)) ->
  rdn RSEGS mem (Z_to_bv 64 0xbd900) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x391bc)) ->
  rdn RSEGS mem (Z_to_bv 64 0xc4db8) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0xc38c8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xa6f7c)) ->
  rdn RSEGS mem (Z_to_bv 64 0xc38d0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0xc4a78) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xc4a78)) ->
  exists regs',
    msteps RSEGS (mkst regs (0xa7114 : word) mem rom)
                 (mkst regs' (0xac8a4 : word) (mem_w2 mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0xa71cc
    /\ getr regs' 9 = s1v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hra Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mg2 Mdso.
  unfold mem_w2. eexists. split.
  -
    stepn F_a5324 D_a5324. rewrite Hsp. sp_renorm.
    stepST F_a5328 D_a5328 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0xa71c8) ltac:(sok_stack SOK).
    stepST F_a532c D_a532c (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_a5330 D_a5330 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).

    stepn F_a5334 D_a5334.
    stepn F_a5338 D_a5338.
    stepLD8 F_a533c D_a533c (Z_to_bv 64 0xbd908).
    stepLD8 F_a5340 D_a5340 (Z_to_bv 64 0xbd900).

    stepb_ft F_a5344 D_a5344 ltac:(cond_compute).

    stepLD8 F_a5348 D_a5348 (Z_to_bv 64 0x391bc).
    stepn F_a534c D_a534c.
    stepjr F_a5350 D_a5350 (Z_to_bv 64 0x391bc) ltac:(gres; reflexivity). vnorm.

    stepn F_38e84 D_38e84. sp_renorm.
    stepST F_38e88 D_38e88 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0xa7144) ltac:(sok_stack SOK).
    stepST F_38e8c D_38e8c (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0xbd900) ltac:(sok_stack SOK).
    stepn F_38e90 D_38e90.
    stepn F_38e94 D_38e94.
    stepn F_38e98 D_38e98.

    stepLBU F_38e9c D_38e9c (Z_to_bv 8 0) ltac:(rewrite v_addi_0; rdn_by Mcomp).
    stepn F_38ea0 D_38ea0.
    stepb_tk F_38ea4 D_38ea4 ltac:(cond_compute).
    stepn F_38eb0 D_38eb0.
    stepn F_38eb4 D_38eb4.
    stepn F_38eb8 D_38eb8.

    stepST F_38ebc D_38ebc (Z_to_bv 64 0xc4db8) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).

    stepn F_38ec0 D_38ec0.
    stepLD8 F_38ec4 D_38ec4 (Z_to_bv 64 0xa6f7c).
    stepb_ft F_38ec8 D_38ec8 ltac:(cond_compute).
    stepn F_38ecc D_38ecc.
    stepn F_38ed0 D_38ed0.
    stepn F_38ed4 D_38ed4.
    stepLD8 F_38ed8 D_38ed8 (Z_to_bv 64 0xc4a78).
    stepn F_38edc D_38edc.
    stepret F_a518c D_a518c (0x39218 : word) ltac:(bveq).
    stepn F_38ee0 D_38ee0.

    stepn F_38ee4 D_38ee4.
    stepLD8 F_38ee8 D_38ee8 (Z_to_bv 64 0).
    stepb_tk F_38eec D_38eec ltac:(cond_compute).

    stepLD8 F_38f04 D_38f04 (Z_to_bv 64 0xa7144).
    stepLD8 F_38f08 D_38f08 (Z_to_bv 64 0xbd900).
    stepn F_38f0c D_38f0c. sp_renorm.
    stepret F_38f10 D_38f10 (0xa7144 : word) ltac:(bveq).

    stepn F_a5354 D_a5354.
    stepb_ft F_a5358 D_a5358 ltac:(cond_compute).
    stepLD8 F_a535c D_a535c (Z_to_bv 64 0xa71c8).
    stepLD8 F_a5360 D_a5360 code.
    stepLD8 F_a5364 D_a5364 s1v.
    stepn F_a5368 D_a5368. sp_renorm.

    stepn F_a536c D_a536c.
    stepret F_a5320 D_a5320 (0xa71c8 : word) ltac:(bveq).
    stepn F_a53d8 D_a53d8.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
