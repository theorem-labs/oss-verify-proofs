(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver Require Import LibWritevG.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require Import LibAtomic.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc Require Import Reloc RelocKit.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Musl Require Import MuslTac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Musl Require StdioDefs Exit.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require Import O9Kit O9_code_exitpath.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module O9Exit.
Import O9Kit.O9ExitBase.
Import O9Kit.O9StdioDefs.
Import O9Kit.O9Reloc.
Import O9Kit.O9RelocCode.
Import O9Kit.O9RelocSites.
Import O9Kit.O9RelocImg.
Import O9Kit.O9RelocMusl.

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
    (Z_to_bv 64 0x11ff10) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0xd7730)))
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
  rdn RSEGS mem (Z_to_bv 64 0x11ff10) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x11ff3b) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0xd76cc : word) mem rom)
                 (mkst regs' (0xd7514 : word)
                       (mem_wA mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 64)
    /\ getr regs' 8 = Z_to_bv 64 0x11fcf4
    /\ getr regs' 18 = Z_to_bv 64 0x11fcf0.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl.
  unfold mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepn F_d7684 D_d7684. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_d7688 D_d7688 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_d768c D_d768c (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_d7690 D_d7690.
    stepn F_d7694 D_d7694. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_d7698 D_d7698 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_d769c D_d769c.
    stepn F_d76a0 D_d76a0.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_d76a4 | reflexivity | exact D_d76a4
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_d76a8 | reflexivity | exact D_d76a8 | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_d76ac | reflexivity | exact D_d76ac
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_d76b0 D_d76b0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_d76b4 D_d76b4.
    (* [comment removed for export] *)
    stepb_ft F_d76b8 D_d76b8 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_d76bc D_d76bc ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_d76e0 D_d76e0. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_d76e4 D_d76e4.
    (* [comment removed for export] *)
    stepn F_d74a0 D_d74a0. sp_renorm.
    stepST F_d74a4 D_d74a4 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0xd7730) ltac:(sok_stack SOK).
    stepST F_d74a8 D_d74a8 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_d74ac D_d74ac (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_d74b0 D_d74b0 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_d74b4 D_d74b4 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_d74b8 D_d74b8.
    stepn F_d74bc D_d74bc.
    stepn F_d74c0 D_d74c0.
    stepn F_d74c4 D_d74c4.
    stepn F_d74c8 D_d74c8.
    (* [comment removed for export] *)
    stepn F_e6a10 D_e6a10.
    stepLB0 F_e6a14 D_e6a14.
    stepb_tk F_e6a18 D_e6a18 ltac:(cond_compute).
    stepretL F_e6c08 D_e6c08 (0xd7514 : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wN (m : word -> option byte) := wbytes m (Z_to_bv 64 0x11fcf0) [Z_to_bv 8 1].

Section VN.
  Context {fx : FPState}.
Lemma wN : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x11fcf4 -> getr regs 18 = Z_to_bv 64 0x11fcf0 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x11fd00) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x11fcf4) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0xd7514 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0xd7730 : word) (mem_wN (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Malock.
  unfold mem_wN, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_d74cc D_d74cc (Z_to_bv 64 0).
    stepb_tk F_d74d0 D_d74d0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_d7540 D_d7540.
    stepST F_d7544 D_d7544 (Z_to_bv 64 0x11fcf0) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_d7548 D_d7548. rewrite Hs0.
    (* [comment removed for export] *)
    stepLD8 F_d754c D_d754c (Z_to_bv 64 0xd7730).
    stepLD8 F_d7550 D_d7550 code.
    stepLD8 F_d7554 D_d7554 s1v.
    stepLD8 F_d7558 D_d7558 s2v.
    stepLD8 F_d755c D_d755c s3v.
    stepn F_d7560 D_d7560. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_d7564 D_d7564.
    stepLW F_e6c98 D_e6c98 0%Z.
    stepb_ft F_e6c9c D_e6c9c ltac:(cond_compute).
    stepretL F_e6ca0 D_e6ca0 (0xd7730 : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wO (m : word -> option byte) :=
  wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 0x11fcf8) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x11fcf8) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0x11fcf8) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x11fd00) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x11fcf0) [Z_to_bv 8 1].

Section VO.
  Context {fx : FPState}.
Lemma wO : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x11fcf4 -> getr regs 18 = Z_to_bv 64 0x11fcf0 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x11fd00) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x11fd08)) ->
  rdn RSEGS mem (Z_to_bv 64 0x11fcf8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
  rdn RSEGS mem (Z_to_bv 64 0x11fd08) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x11fd10) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xd7678)) ->
  rdn RSEGS mem (Z_to_bv 64 0x11fe10) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x5ccd8)) ->
  rdn RSEGS mem (Z_to_bv 64 0xff9f4) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x11fcf4) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x11ff3b) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0xd7514 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0xd7730 : word) (mem_wO (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Mslot Mnext Mf0 Ma0 Mcb Malock Mnl.
  unfold mem_wO, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_d74cc D_d74cc (Z_to_bv 64 0x11fd08).
    stepb_ft F_d74d0 D_d74d0 ltac:(cond_compute).
    stepLW F_d74d4 D_d74d4 1%Z.
    stepn F_d74d8 D_d74d8.
    (* [comment removed for export] *)
    stepn F_d74f0 D_d74f0.
    stepST F_d74f4 D_d74f4 (Z_to_bv 64 0x11fcf8) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_d74f8 D_d74f8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_d74fc D_d74fc (Z_to_bv 64 0x11fd08).
    stepn F_d7500 D_d7500.
    stepn F_d7504 D_d7504.
    stepLD8 F_d7508 D_d7508 (Z_to_bv 64 0xd7678).
    stepLD8 F_d750c D_d750c (Z_to_bv 64 0x5ccd8).
    (* [comment removed for export] *)
    stepn F_d7510 D_d7510. rewrite Hs0.
    stepn F_d7514 D_d7514.
    stepLW F_e6c98 D_e6c98 0%Z.
    stepb_ft F_e6c9c D_e6c9c ltac:(cond_compute).
    stepretL F_e6ca0 D_e6ca0 (0xd7560 : word).
    (* [comment removed for export] *)
    stepn F_d7518 D_d7518.
    stepretL F_d751c D_d751c (0xd7678 : word).
    stepretL F_d7630 D_d7630 (0x5ccd8 : word).
    (* [comment removed for export] *)
    stepn F_5cc80 D_5cc80.
    stepLBU F_5cc84 D_5cc84 (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_5cc88 D_5cc88 ltac:(cond_compute).
    stepretL F_5cc8c D_5cc8c (0xd7568 : word).
    (* [comment removed for export] *)
    stepn F_d7520 D_d7520.
    stepn F_d7524 D_d7524.
    stepn F_e6a10 D_e6a10.
    stepLB0 F_e6a14 D_e6a14.
    stepb_tk F_e6a18 D_e6a18 ltac:(cond_compute).
    stepretL F_e6c08 D_e6c08 (0xd7570 : word).
    (* [comment removed for export] *)
    stepLW F_d7528 D_d7528 0%Z.
    stepn F_d752c D_d752c.
    stepST F_d7530 D_d7530 (Z_to_bv 64 0x11fcf8) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_d7534 D_d7534 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_d7538 D_d7538 (Z_to_bv 64 0x11fd08).
    stepn F_d753c D_d753c.
    stepLD8 F_d74dc D_d74dc (Z_to_bv 64 0).
    stepn F_d74e0 D_d74e0.
    stepST F_d74e4 D_d74e4 (Z_to_bv 64 0x11fcf8) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_d74e8 D_d74e8 (Z_to_bv 64 0x11fd00) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_d74ec D_d74ec ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_d7540 D_d7540.
    stepST F_d7544 D_d7544 (Z_to_bv 64 0x11fcf0) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_d7548 D_d7548.
    (* [comment removed for export] *)
    stepLD8 F_d754c D_d754c (Z_to_bv 64 0xd7730).
    stepLD8 F_d7550 D_d7550 code.
    stepLD8 F_d7554 D_d7554 s1v.
    stepLD8 F_d7558 D_d7558 s2v.
    stepLD8 F_d755c D_d755c s3v.
    stepn F_d7560 D_d7560. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_d7564 D_d7564.
    stepLW F_e6c98 D_e6c98 0%Z.
    stepb_ft F_e6c9c D_e6c9c ltac:(cond_compute).
    stepretL F_e6ca0 D_e6ca0 (0xd7730 : word).
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
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0xd7734)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0xd76b0)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0xeb198)))
    (Z_to_bv 64 0xef9e8) [Z_to_bv 8 1].

Section V2R.
  Context {fx : FPState}.
Lemma w2R : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0xee700) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xeb1a0)) ->
  rdn RSEGS mem (Z_to_bv 64 0xee708) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xeb198)) ->
  rdn RSEGS mem (Z_to_bv 64 0xeb198) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x5c820)) ->
  rdn RSEGS mem (Z_to_bv 64 0xef9e8) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0xee540) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xd75b0)) ->
  rdn RSEGS mem (Z_to_bv 64 0xee548) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0xef728) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xef728)) ->
  exists regs',
    msteps RSEGS (mkst regs (0xd7730 : word) mem rom)
                 (mkst regs' (0xdb40c : word) (mem_w2R mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0xd7738.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mg2 Mdso.
  unfold mem_w2R. eexists. split.
  - (* [comment removed for export] *)
    stepn F_d76e8 D_d76e8.
    stepn F_d7638 D_d7638. rewrite Hsp. sp_renorm.
    stepST F_d763c D_d763c (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0xd7734) ltac:(sok_stack SOK).
    stepST F_d7640 D_d7640 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_d7644 D_d7644 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_d7648 D_d7648.
    stepn F_d764c D_d764c.
    stepLD8 F_d7650 D_d7650 (Z_to_bv 64 0xeb1a0).
    stepLD8 F_d7654 D_d7654 (Z_to_bv 64 0xeb198).
    (* [comment removed for export] *)
    stepb_ft F_d7658 D_d7658 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_d765c D_d765c (Z_to_bv 64 0x5c820).
    stepn F_d7660 D_d7660.
    stepretL F_d7664 D_d7664 (0x5c820 : word).
    (* [comment removed for export] *)
    stepn F_5c7c8 D_5c7c8. sp_renorm.
    stepST F_5c7cc D_5c7cc (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0xd76b0) ltac:(sok_stack SOK).
    stepST F_5c7d0 D_5c7d0 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0xeb198) ltac:(sok_stack SOK).
    stepn F_5c7d4 D_5c7d4.
    stepn F_5c7d8 D_5c7d8.
    stepn F_5c7dc D_5c7dc.
    (* [comment removed for export] *)
    stepLBU F_5c7e0 D_5c7e0 (Z_to_bv 8 0) ltac:(rewrite ?v_addi_0; rdn_by Mcomp).
    stepn F_5c7e4 D_5c7e4.
    stepb_tk F_5c7e8 D_5c7e8 ltac:(cond_compute).
    stepn F_5c7f4 D_5c7f4.
    stepn F_5c7f8 D_5c7f8.
    stepn F_5c7fc D_5c7fc.
    (* [comment removed for export] *)
    stepST F_5c800 D_5c800 (Z_to_bv 64 0xef9e8) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_5c804 D_5c804.
    stepLD8 F_5c808 D_5c808 (Z_to_bv 64 0xd75b0).
    stepb_ft F_5c80c D_5c80c ltac:(cond_compute).
    stepn F_5c810 D_5c810.
    stepn F_5c814 D_5c814.
    stepn F_5c818 D_5c818.
    stepLD8 F_5c81c D_5c81c (Z_to_bv 64 0xef728).
    stepn F_5c820 D_5c820.
    stepretL F_d7568 D_d7568 (0x5c87c : word).
    stepn F_5c824 D_5c824.
    (* [comment removed for export] *)
    stepn F_5c828 D_5c828.
    stepLD8 F_5c82c D_5c82c (Z_to_bv 64 0).
    stepb_tk F_5c830 D_5c830 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_5c848 D_5c848 (Z_to_bv 64 0xd76b0).
    stepLD8 F_5c84c D_5c84c (Z_to_bv 64 0xeb198).
    stepn F_5c850 D_5c850. sp_renorm.
    stepretL F_5c854 D_5c854 (0xd76b0 : word).
    (* [comment removed for export] *)
    stepn F_d7668 D_d7668.
    stepb_ft F_d766c D_d766c ltac:(cond_compute).
    stepLD8 F_d7670 D_d7670 (Z_to_bv 64 0xd7734).
    stepLD8 F_d7674 D_d7674 code.
    stepLD8 F_d7678 D_d7678 s1v.
    stepn F_d767c D_d767c. sp_renorm.
    (* [comment removed for export] *)
    stepn F_d7680 D_d7680.
    stepretL F_d7634 D_d7634 (0xd7734 : word).
    stepn F_d76ec D_d76ec.
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
    msteps RSEGS (mkst regs (0xd76cc : word) mem rom) (mkst regs' (0xdb40c : word) mem' rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0xd7738
    /\ store_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true
    /\ (forall (a : Z) n bs, rdn RSEGS mem (Z_to_bv 64 a) n = Some bs ->
          (0 <= a)%Z -> (a + Z.of_nat n <= 0x121000)%Z ->
          (a + Z.of_nat n <= 0xef9e8 \/ 0xef9e9 <= a)%Z ->
          (a + Z.of_nat n <= 0x11fcf0 \/ 0x11fd08 <= a)%Z ->
          (a + Z.of_nat n <= 0x11ff10 \/ 0x11ff14 <= a)%Z ->
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
  file_clean mem 0xef888 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0xd76cc : word) mem (seg_rom RSEGS)) model)
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
  assert (FC1 : file_clean mem1 0xef888 wp1 rp1).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (FC2 : file_clean mem1 0xef798 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_clean fx o9_reloc o9_code o9_sites o9_data o9_rw
             regs1 mem1 model sp code wp1 rp1 wp2 rp2 Rsp Rs0 Rra Esplo Esphi SOK1 G1 FC1 FC2 Hh Hlazy).
Qed.
End VP1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stdout_pending_G : forall mem wb wp bufp bufsz rp1 can pending,
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  @StdioDefs.stdout_pending o9_reloc mem wb wp bufp bufsz rp1 can pending.
Proof.
  intros mem wb wp bufp bufsz rp1 can pending [f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14].
  exact (@StdioDefs.Build_stdout_pending o9_reloc mem wb wp bufp bufsz rp1 can pending
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
  realizes RSEGS (mkCfg (mkst regs (0xd76cc : word) mem (seg_rom RSEGS)) model)
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
  assert (FC2 : file_clean mem1 0xef798 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (SP1 : stdout_pending mem1 wb wp bufp bufsz rp1 can pending).
  { constructor; zaddr_goal; try assumption.
    1-9: (apply TR; [assumption | cbn; lia ..]).
    - apply TR; [assumption | lia ..].
    - split; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_flush fx o9_reloc o9_code o9_sites o9_data o9_rw
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
  realizes RSEGS (mkCfg (mkst regs (0xd76cc : word) mem (seg_rom RSEGS)) model)
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
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0xd76cc) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending PRE.
  replace (Z_to_bv 64 0xd76cc) with (0xd76cc : word) by (apply bv_eq; reflexivity).
  exact (ref_exit regs mem model code pending PRE).
Qed.
End VP5.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End O9Exit.
