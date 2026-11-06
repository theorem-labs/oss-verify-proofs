(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.grayquant_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import LibWritevG.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import LibAtomic.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc Require Import Reloc RelocKit.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Musl Require Import MuslTac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Musl Require StdioDefs Exit.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require Import O15Kit O15_code_exitpath.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module O15Exit.
Import O15Kit.O15ExitBase.
Import O15Kit.O15StdioDefs.
Import O15Kit.O15Reloc.
Import O15Kit.O15RelocCode.
Import O15Kit.O15RelocSites.
Import O15Kit.O15RelocImg.
Import O15Kit.O15RelocMusl.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac zaddr_rec H := zaddr H.

(* [comment removed for export] *)
Ltac stepLB0 F D :=
  chain_step; [reflexivity
    | eapply step_lb with (b := Z_to_bv 8 0);
      [exact F | reflexivity | exact D | gres; imm_norm; addr_norm; rdn_solve]
    | step_simpl]; vnorm.
Ltac stepretL F D k := stepret F D k ltac:(first [reflexivity | bveq]).
(* [comment removed for export] *)
Ltac rdn_solve4 :=
  lazymatch goal with
  | |- rdn _ (wbytes _ ?a _) ?b 4%nat = _ =>
      tryif constr_eq a b then (apply WalksLib.rdn_wbytes_hit4; zsimp; lia)
      else (rdn_peel1; rdn_solve4)
  | |- _ => rdn_hyp
  end.
Ltac stepLW F D z :=
  stepLD F D (word_to_le_bytes 4 (Z_to_bv 64 z)) (Z_to_bv 64 z)
    ltac:(addr_norm; rdn_solve4) ltac:(apply bytes_le_to_Z_4; u_norm; lia);
  try rewrite (v_lw_small z) by lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mem_wA (mem : word -> option byte) (sp ra s0v code s1v s2v s3v : word) (tid : Z) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (bv_unsigned sp - 16)) (word_to_le_bytes 8 s0v))
    (Z_to_bv 64 0x5ddb0) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x20d04)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3v).

Section VA.
  Context {fx : FPState}.
Lemma wA : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5ddb0) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5dddb) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x20ca0 : word) mem rom)
                 (mkst regs' (0x20ae8 : word)
                       (mem_wA mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 64)
    /\ getr regs' 8 = Z_to_bv 64 0x5db94
    /\ getr regs' 18 = Z_to_bv 64 0x5db90.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl.
  unfold mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepn F_20c54 D_20c54. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_20c58 D_20c58 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_20c5c D_20c5c (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_20c60 D_20c60.
    stepn F_20c64 D_20c64. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_20c68 D_20c68 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_20c6c D_20c6c.
    stepn F_20c70 D_20c70.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_20c74 | reflexivity | exact D_20c74
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_20c78 | reflexivity | exact D_20c78 | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_20c7c | reflexivity | exact D_20c7c
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_20c80 D_20c80 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_20c84 D_20c84.
    (* [comment removed for export] *)
    stepb_ft F_20c88 D_20c88 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_20c8c D_20c8c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_20cb0 D_20cb0. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_20cb4 D_20cb4.
    (* [comment removed for export] *)
    stepn F_20a70 D_20a70. sp_renorm.
    stepST F_20a74 D_20a74 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x20d04) ltac:(sok_stack SOK).
    stepST F_20a78 D_20a78 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_20a7c D_20a7c (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_20a80 D_20a80 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_20a84 D_20a84 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_20a88 D_20a88.
    stepn F_20a8c D_20a8c.
    stepn F_20a90 D_20a90.
    stepn F_20a94 D_20a94.
    stepn F_20a98 D_20a98.
    (* [comment removed for export] *)
    stepn F_2b2e8 D_2b2e8.
    stepLB0 F_2b2ec D_2b2ec.
    stepb_tk F_2b2f0 D_2b2f0 ltac:(cond_compute).
    stepretL F_2b4e0 D_2b4e0 (0x20ae8 : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wN (m : word -> option byte) := wbytes m (Z_to_bv 64 0x5db90) [Z_to_bv 8 1].

Section VN.
  Context {fx : FPState}.
Lemma wN : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x5db94 -> getr regs 18 = Z_to_bv 64 0x5db90 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x5dba0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5db94) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x20ae8 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0x20d04 : word) (mem_wN (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Malock.
  unfold mem_wN, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_20a9c D_20a9c (Z_to_bv 64 0).
    stepb_tk F_20aa0 D_20aa0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_20b10 D_20b10.
    stepST F_20b14 D_20b14 (Z_to_bv 64 0x5db90) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_20b18 D_20b18. rewrite Hs0.
    (* [comment removed for export] *)
    stepLD8 F_20b1c D_20b1c (Z_to_bv 64 0x20d04).
    stepLD8 F_20b20 D_20b20 code.
    stepLD8 F_20b24 D_20b24 s1v.
    stepLD8 F_20b28 D_20b28 s2v.
    stepLD8 F_20b2c D_20b2c s3v.
    stepn F_20b30 D_20b30. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_20b34 D_20b34.
    stepLW F_2b570 D_2b570 0%Z.
    stepb_ft F_2b574 D_2b574 ltac:(cond_compute).
    stepretL F_2b578 D_2b578 (0x20d04 : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wO (m : word -> option byte) :=
  wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 0x5db98) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x5db98) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0x5db98) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x5dba0) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x5db90) [Z_to_bv 8 1].

Section VO.
  Context {fx : FPState}.
Lemma wO : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x5db94 -> getr regs 18 = Z_to_bv 64 0x5db90 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x5dba0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x5dba8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5db98) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5dba8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5dbb0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x20c4c)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5dcb0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1518c)) ->
  rdn RSEGS mem (Z_to_bv 64 0x3da54) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x5db94) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5dddb) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x20ae8 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0x20d04 : word) (mem_wO (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Mslot Mnext Mf0 Ma0 Mcb Malock Mnl.
  unfold mem_wO, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_20a9c D_20a9c (Z_to_bv 64 0x5dba8).
    stepb_ft F_20aa0 D_20aa0 ltac:(cond_compute).
    stepLW F_20aa4 D_20aa4 1%Z.
    stepn F_20aa8 D_20aa8.
    (* [comment removed for export] *)
    stepn F_20ac0 D_20ac0.
    stepST F_20ac4 D_20ac4 (Z_to_bv 64 0x5db98) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_20ac8 D_20ac8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_20acc D_20acc (Z_to_bv 64 0x5dba8).
    stepn F_20ad0 D_20ad0.
    stepn F_20ad4 D_20ad4.
    stepLD8 F_20ad8 D_20ad8 (Z_to_bv 64 0x20c4c).
    stepLD8 F_20adc D_20adc (Z_to_bv 64 0x1518c).
    (* [comment removed for export] *)
    stepn F_20ae0 D_20ae0. rewrite Hs0.
    stepn F_20ae4 D_20ae4.
    stepLW F_2b570 D_2b570 0%Z.
    stepb_ft F_2b574 D_2b574 ltac:(cond_compute).
    stepretL F_2b578 D_2b578 (0x20b34 : word).
    (* [comment removed for export] *)
    stepn F_20ae8 D_20ae8.
    stepretL F_20aec D_20aec (0x20c4c : word).
    stepretL F_20c00 D_20c00 (0x1518c : word).
    (* [comment removed for export] *)
    stepn F_15134 D_15134.
    stepLBU F_15138 D_15138 (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_1513c D_1513c ltac:(cond_compute).
    stepretL F_15140 D_15140 (0x20b3c : word).
    (* [comment removed for export] *)
    stepn F_20af0 D_20af0.
    stepn F_20af4 D_20af4.
    stepn F_2b2e8 D_2b2e8.
    stepLB0 F_2b2ec D_2b2ec.
    stepb_tk F_2b2f0 D_2b2f0 ltac:(cond_compute).
    stepretL F_2b4e0 D_2b4e0 (0x20b44 : word).
    (* [comment removed for export] *)
    stepLW F_20af8 D_20af8 0%Z.
    stepn F_20afc D_20afc.
    stepST F_20b00 D_20b00 (Z_to_bv 64 0x5db98) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_20b04 D_20b04 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_20b08 D_20b08 (Z_to_bv 64 0x5dba8).
    stepn F_20b0c D_20b0c.
    stepLD8 F_20aac D_20aac (Z_to_bv 64 0).
    stepn F_20ab0 D_20ab0.
    stepST F_20ab4 D_20ab4 (Z_to_bv 64 0x5db98) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_20ab8 D_20ab8 (Z_to_bv 64 0x5dba0) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_20abc D_20abc ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_20b10 D_20b10.
    stepST F_20b14 D_20b14 (Z_to_bv 64 0x5db90) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_20b18 D_20b18.
    (* [comment removed for export] *)
    stepLD8 F_20b1c D_20b1c (Z_to_bv 64 0x20d04).
    stepLD8 F_20b20 D_20b20 code.
    stepLD8 F_20b24 D_20b24 s1v.
    stepLD8 F_20b28 D_20b28 s2v.
    stepLD8 F_20b2c D_20b2c s3v.
    stepn F_20b30 D_20b30. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_20b34 D_20b34.
    stepLW F_2b570 D_2b570 0%Z.
    stepb_ft F_2b574 D_2b574 ltac:(cond_compute).
    stepretL F_2b578 D_2b578 (0x20d04 : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VO.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mem_w2R (mem : word -> option byte) (sp code s1v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x20d08)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x20c84)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x2c710)))
    (Z_to_bv 64 0x2da48) [Z_to_bv 8 1].

Section V2R.
  Context {fx : FPState}.
Lemma w2R : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x2c7b8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2c718)) ->
  rdn RSEGS mem (Z_to_bv 64 0x2c7c0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2c710)) ->
  rdn RSEGS mem (Z_to_bv 64 0x2c710) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x14cd4)) ->
  rdn RSEGS mem (Z_to_bv 64 0x2da48) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x2c758) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x20b84)) ->
  rdn RSEGS mem (Z_to_bv 64 0x2c760) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x2d7c8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2d7c8)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x20d04 : word) mem rom)
                 (mkst regs' (0x22f88 : word) (mem_w2R mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x20d0c.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mg2 Mdso.
  unfold mem_w2R. eexists. split.
  - (* [comment removed for export] *)
    stepn F_20cb8 D_20cb8.
    stepn F_20c08 D_20c08. rewrite Hsp. sp_renorm.
    stepST F_20c0c D_20c0c (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x20d08) ltac:(sok_stack SOK).
    stepST F_20c10 D_20c10 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_20c14 D_20c14 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_20c18 D_20c18.
    stepn F_20c1c D_20c1c.
    stepLD8 F_20c20 D_20c20 (Z_to_bv 64 0x2c718).
    stepLD8 F_20c24 D_20c24 (Z_to_bv 64 0x2c710).
    (* [comment removed for export] *)
    stepb_ft F_20c28 D_20c28 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_20c2c D_20c2c (Z_to_bv 64 0x14cd4).
    stepn F_20c30 D_20c30.
    stepretL F_20c34 D_20c34 (0x14cd4 : word).
    (* [comment removed for export] *)
    stepn F_14c7c D_14c7c. sp_renorm.
    stepST F_14c80 D_14c80 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x20c84) ltac:(sok_stack SOK).
    stepST F_14c84 D_14c84 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x2c710) ltac:(sok_stack SOK).
    stepn F_14c88 D_14c88.
    stepn F_14c8c D_14c8c.
    stepn F_14c90 D_14c90.
    (* [comment removed for export] *)
    stepLBU F_14c94 D_14c94 (Z_to_bv 8 0) ltac:(rewrite ?v_addi_0; rdn_by Mcomp).
    stepn F_14c98 D_14c98.
    stepb_tk F_14c9c D_14c9c ltac:(cond_compute).
    stepn F_14ca8 D_14ca8.
    stepn F_14cac D_14cac.
    stepn F_14cb0 D_14cb0.
    (* [comment removed for export] *)
    stepST F_14cb4 D_14cb4 (Z_to_bv 64 0x2da48) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_14cb8 D_14cb8.
    stepLD8 F_14cbc D_14cbc (Z_to_bv 64 0x20b84).
    stepb_ft F_14cc0 D_14cc0 ltac:(cond_compute).
    stepn F_14cc4 D_14cc4.
    stepn F_14cc8 D_14cc8.
    stepn F_14ccc D_14ccc.
    stepLD8 F_14cd0 D_14cd0 (Z_to_bv 64 0x2d7c8).
    stepn F_14cd4 D_14cd4.
    stepretL F_20b38 D_20b38 (0x14d30 : word).
    stepn F_14cd8 D_14cd8.
    (* [comment removed for export] *)
    stepn F_14cdc D_14cdc.
    stepLD8 F_14ce0 D_14ce0 (Z_to_bv 64 0).
    stepb_tk F_14ce4 D_14ce4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_14cfc D_14cfc (Z_to_bv 64 0x20c84).
    stepLD8 F_14d00 D_14d00 (Z_to_bv 64 0x2c710).
    stepn F_14d04 D_14d04. sp_renorm.
    stepretL F_14d08 D_14d08 (0x20c84 : word).
    (* [comment removed for export] *)
    stepn F_20c38 D_20c38.
    stepb_ft F_20c3c D_20c3c ltac:(cond_compute).
    stepLD8 F_20c40 D_20c40 (Z_to_bv 64 0x20d08).
    stepLD8 F_20c44 D_20c44 code.
    stepLD8 F_20c48 D_20c48 s1v.
    stepn F_20c4c D_20c4c. sp_renorm.
    (* [comment removed for export] *)
    stepn F_20c50 D_20c50.
    stepretL F_20c04 D_20c04 (0x20d08 : word).
    stepn F_20cbc D_20cbc.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End V2R.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section VPRE.
  Context {fx : FPState}.
Lemma w_pre : forall regs mem rom (sp tp code : word) (tid : Z) (wp2 rp2 : word),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  exists regs' mem',
    msteps RSEGS (mkst regs (0x20ca0 : word) mem rom) (mkst regs' (0x22f88 : word) mem' rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x20d0c
    /\ store_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true
    /\ (forall (a : Z) n bs, rdn RSEGS mem (Z_to_bv 64 a) n = Some bs ->
          (0 <= a)%Z -> (a + Z.of_nat n <= 0x5f000)%Z ->
          (a + Z.of_nat n <= 0x2da48 \/ 0x2da49 <= a)%Z ->
          (a + Z.of_nat n <= 0x5db90 \/ 0x5dba8 <= a)%Z ->
          (a + Z.of_nat n <= 0x5ddb0 \/ 0x5ddb4 <= a)%Z ->
          rdn RSEGS mem' (Z_to_bv 64 a) n = Some bs).
Proof.
  intros regs mem rom sp tp code tid wp2 rp2
    [Esp Etp Ea0 Esplo Esphi Esok Etplo Etphi Etid Emtid Elock Efe Efs Efa Ecomp Eg1 Eg2 Eglob Eerr Edso Ealock Eatexit].
  destruct Eglob as (Gnl & Gofl & Gin & Gout & Gerr).
  destruct (wA regs mem rom sp tp code tid) as (regsA & RUNA & RAsp & RAs0 & RAs2); try assumption.
  set (mA := mem_wA mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) in *.
  destruct Eatexit as [AN | (AOh & AOs & AOn & AOf & AOa & AOc)].
  - (* [comment removed for export] *)
    destruct (wN regsA mem rom sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid)
      as (regsB & RUNB & RBsp & RBs0 & RBs1 & RBs2 & RBs3); try assumption.
    fold mA in RUNB.
    destruct (w2R regsB (mem_wN mA) rom sp code (getr regs 9))
      as (regsC & RUNC & RCsp & RCs0 & RCra); try assumption.
    all: try (subst mA; unfold mem_wN, mem_wA; first [store_ok_peel; exact Esok | rdn_solve]).
    exists regsC, (mem_w2R (mem_wN mA) sp code (getr regs 9)).
    split; [eapply msteps_trans; [exact RUNA | eapply msteps_trans; [exact RUNB | exact RUNC]] |].
    split; [exact RCsp|]. split; [exact RCs0|]. split; [exact RCra|].
    split.
    + subst mA; unfold mem_w2R, mem_wN, mem_wA; store_ok_peel; exact Esok.
    + intros a n bs Hr A0 Ahi D1 D2 D3.
      subst mA; unfold mem_w2R, mem_wN, mem_wA.
      repeat (rewrite rdn_wbytes_out_Z by (zlen; lia)). exact Hr.
  - (* [comment removed for export] *)
    destruct (wO regsA mem rom sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid)
      as (regsB & RUNB & RBsp & RBs0 & RBs1 & RBs2 & RBs3); try assumption.
    fold mA in RUNB.
    destruct (w2R regsB (mem_wO mA) rom sp code (getr regs 9))
      as (regsC & RUNC & RCsp & RCs0 & RCra); try assumption.
    all: try (subst mA; unfold mem_wO, mem_wA; first [store_ok_peel; exact Esok | rdn_solve]).
    exists regsC, (mem_w2R (mem_wO mA) sp code (getr regs 9)).
    split; [eapply msteps_trans; [exact RUNA | eapply msteps_trans; [exact RUNB | exact RUNC]] |].
    split; [exact RCsp|]. split; [exact RCs0|]. split; [exact RCra|].
    split.
    + subst mA; unfold mem_w2R, mem_wO, mem_wA; store_ok_peel; exact Esok.
    + intros a n bs Hr A0 Ahi D1 D2 D3.
      subst mA; unfold mem_w2R, mem_wO, mem_wA.
      repeat (rewrite rdn_wbytes_out_Z by (zlen; lia)). exact Hr.
Qed.
End VPRE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section VP1.
  Context {fx : FPState}.
Theorem ref_exit_clean :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 wp1 rp1 : word),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  file_clean mem 0x2d900 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0x20ca0 : word) mem (seg_rom RSEGS)) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wp1 rp1 EC F1 Hh Hlazy.
  destruct (w_pre regs mem (seg_rom RSEGS) sp tp code tid wp2 rp2 EC)
    as (regs1 & mem1 & RUN & Rsp & Rs0 & Rra & SOK1 & TR).
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
  destruct EC as [Esp Etp Ea0 Esplo Esphi Esok Etplo Etphi Etid Emtid Elock Efe Efs Efa Ecomp Eg1 Eg2 Eglob Eerr Edso Ealock Eatexit].
  destruct Eglob as (Gnl & Gofl & Gin & Gout & Gerr).
  destruct Eerr as (F2l & F2wp & F2wb & F2rp & F2re).
  destruct F1 as (F1l & F1wp & F1wb & F1rp & F1re).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  assert (G1 : stdio_globals mem1).
  { repeat split; (apply TR; [assumption | cbn; lia ..]). }
  assert (FC1 : file_clean mem1 0x2d900 wp1 rp1).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (FC2 : file_clean mem1 0x2d810 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_clean fx o15_reloc o15_code o15_sites o15_data o15_rw
             regs1 mem1 model sp code wp1 rp1 wp2 rp2 Rsp Rs0 Rra Esplo Esphi SOK1 G1 FC1 FC2 Hh Hlazy).
Qed.
End VP1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stdout_pending_G : forall mem wb wp bufp bufsz rp1 can pending,
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  @StdioDefs.stdout_pending o15_reloc mem wb wp bufp bufsz rp1 can pending.
Proof.
  intros mem wb wp bufp bufsz rp1 can pending [f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14].
  exact (@StdioDefs.Build_stdout_pending o15_reloc mem wb wp bufp bufsz rp1 can pending
           f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14).
Qed.

Section VP2.
  Context {fx : FPState}.
Theorem ref_exit_flush :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 : word)
         (wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  realizes RSEGS (mkCfg (mkst regs (0x20ca0 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending EC SP Hh Hlazy Hfd.
  destruct (w_pre regs mem (seg_rom RSEGS) sp tp code tid wp2 rp2 EC)
    as (regs1 & mem1 & RUN & Rsp & Rs0 & Rra & SOK1 & TR).
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
  destruct EC as [Esp Etp Ea0 Esplo Esphi Esok Etplo Etphi Etid Emtid Elock Efe Efs Efa Ecomp Eg1 Eg2 Eglob Eerr Edso Ealock Eatexit].
  destruct Eglob as (Gnl & Gofl & Gin & Gout & Gerr).
  destruct Eerr as (F2l & F2wp & F2wb & F2rp & F2re).
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  destruct SP as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN PMAX BYTES [Ggot Gcan]].
  zaddr P1l; zaddr P1wp; zaddr P1wb; zaddr P1wr; zaddr P1buf; zaddr P1bsz; zaddr P1fd; zaddr P1rp; zaddr P1re.
  assert (G1 : stdio_globals mem1).
  { repeat split; (apply TR; [assumption | cbn; lia ..]). }
  assert (FC2 : file_clean mem1 0x2d810 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (SP1 : stdout_pending mem1 wb wp bufp bufsz rp1 can pending).
  { constructor; zaddr_goal; try assumption.
    1-9: (apply TR; [assumption | cbn; lia ..]).
    - apply TR; [assumption | lia ..].
    - split; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_flush fx o15_reloc o15_code o15_sites o15_data o15_rw
             regs1 mem1 model sp code wp2 rp2 wb wp bufp bufsz rp1 can pending
             Rsp Rs0 Rra Esplo Esphi SOK1 G1 FC2 (stdout_pending_G _ _ _ _ _ _ _ _ SP1) Hh Hlazy Hfd).
Qed.
End VP2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section VP3.
  Context {fx : FPState}.
Lemma t_emit_nil_exit : forall code fs, t_eq (t_exit code fs) (t_emit [] (t_exit code fs)).
Proof.
  intros code fs. apply t_eq_sym. apply t_emit_nil_eq.
  unfold t_exit, t_emit. left. apply is_prefix_nil.
Qed.
End VP3.

Section VP4.
  Context {fx : FPState}.
Theorem ref_exit : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  realizes RSEGS (mkCfg (mkst regs (0x20ca0 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending (sp & tp & tid & wp2 & rp2 & EC & Hh & Hlazy & CASES).
  destruct CASES as [(E & wp1 & rp1 & F1) | (wb & wp & bufp & bufsz & rp1 & can & SP & Hfd)].
  - subst pending. cbn [W map].
    eapply rz_conseq; [| apply t_emit_nil_exit].
    exact (ref_exit_clean regs mem model sp tp code tid wp2 rp2 wp1 rp1 EC F1 Hh Hlazy).
  - exact (ref_exit_flush regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending EC SP Hh Hlazy Hfd).
Qed.
End VP4.

(* [comment removed for export] *)
Section VP5.
  Context {fx : FPState}.
Corollary ref_exit_Z : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x20ca0) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending PRE.
  replace (Z_to_bv 64 0x20ca0) with (0x20ca0 : word) by (apply bv_eq; reflexivity).
  exact (ref_exit regs mem model code pending PRE).
Qed.
End VP5.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End O15Exit.
