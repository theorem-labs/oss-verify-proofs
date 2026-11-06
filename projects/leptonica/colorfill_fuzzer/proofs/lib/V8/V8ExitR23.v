(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.colorfill_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.CliDriver Require Import LibWritevG.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require Import LibAtomic.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Reloc Require Import Reloc RelocKit.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Musl Require Import MuslTac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Musl Require StdioDefs Exit.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require Import V8Kit V8_code_exitpath.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module V8Exit.
Import V8Kit.V8ExitBase.
Import V8Kit.V8StdioDefs.
Import V8Kit.V8Reloc.
Import V8Kit.V8RelocCode.
Import V8Kit.V8RelocSites.
Import V8Kit.V8RelocImg.
Import V8Kit.V8RelocMusl.

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
    (Z_to_bv 64 0x51dd0) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x17980)))
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
  rdn RSEGS mem (Z_to_bv 64 0x51dd0) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x51dfb) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x1791c : word) mem rom)
                 (mkst regs' (0x17764 : word)
                       (mem_wA mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 64)
    /\ getr regs' 8 = Z_to_bv 64 0x51bb4
    /\ getr regs' 18 = Z_to_bv 64 0x51bb0.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl.
  unfold mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepn F_1791c D_1791c. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_17920 D_17920 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_17924 D_17924 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_17928 D_17928.
    stepn F_1792c D_1792c. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_17930 D_17930 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_17934 D_17934.
    stepn F_17938 D_17938.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_1793c | reflexivity | exact D_1793c
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_17940 | reflexivity | exact D_17940 | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_17944 | reflexivity | exact D_17944
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_17948 D_17948 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_1794c D_1794c.
    (* [comment removed for export] *)
    stepb_ft F_17950 D_17950 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_17954 D_17954 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_17978 D_17978. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_1797c D_1797c.
    (* [comment removed for export] *)
    stepn F_17738 D_17738. sp_renorm.
    stepST F_1773c D_1773c (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x17980) ltac:(sok_stack SOK).
    stepST F_17740 D_17740 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_17744 D_17744 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_17748 D_17748 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_1774c D_1774c (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_17750 D_17750.
    stepn F_17754 D_17754.
    stepn F_17758 D_17758.
    stepn F_1775c D_1775c.
    stepn F_17760 D_17760.
    (* [comment removed for export] *)
    stepn F_1f358 D_1f358.
    stepLB0 F_1f35c D_1f35c.
    stepb_tk F_1f360 D_1f360 ltac:(cond_compute).
    stepretL F_1f550 D_1f550 (0x17764 : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wN (m : word -> option byte) := wbytes m (Z_to_bv 64 0x51bb0) [Z_to_bv 8 1].

Section VN.
  Context {fx : FPState}.
Lemma wN : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x51bb4 -> getr regs 18 = Z_to_bv 64 0x51bb0 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x51bc0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x51bb4) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x17764 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0x17980 : word) (mem_wN (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Malock.
  unfold mem_wN, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_17764 D_17764 (Z_to_bv 64 0).
    stepb_tk F_17768 D_17768 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_177d8 D_177d8.
    stepST F_177dc D_177dc (Z_to_bv 64 0x51bb0) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_177e0 D_177e0. rewrite Hs0.
    (* [comment removed for export] *)
    stepLD8 F_177e4 D_177e4 (Z_to_bv 64 0x17980).
    stepLD8 F_177e8 D_177e8 code.
    stepLD8 F_177ec D_177ec s1v.
    stepLD8 F_177f0 D_177f0 s2v.
    stepLD8 F_177f4 D_177f4 s3v.
    stepn F_177f8 D_177f8. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_177fc D_177fc.
    stepLW F_1f5e0 D_1f5e0 0%Z.
    stepb_ft F_1f5e4 D_1f5e4 ltac:(cond_compute).
    stepretL F_1f5e8 D_1f5e8 (0x17980 : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wO (m : word -> option byte) :=
  wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 0x51bb8) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x51bb8) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0x51bb8) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x51bc0) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x51bb0) [Z_to_bv 8 1].

Section VO.
  Context {fx : FPState}.
Lemma wO : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x51bb4 -> getr regs 18 = Z_to_bv 64 0x51bb0 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x51bc0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x51bc8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x51bb8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
  rdn RSEGS mem (Z_to_bv 64 0x51bc8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x51bd0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x178c8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x51cd0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13d30)) ->
  rdn RSEGS mem (Z_to_bv 64 0x31a74) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x51bb4) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x51dfb) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x17764 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0x17980 : word) (mem_wO (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Mslot Mnext Mf0 Ma0 Mcb Malock Mnl.
  unfold mem_wO, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_17764 D_17764 (Z_to_bv 64 0x51bc8).
    stepb_ft F_17768 D_17768 ltac:(cond_compute).
    stepLW F_1776c D_1776c 1%Z.
    stepn F_17770 D_17770.
    (* [comment removed for export] *)
    stepn F_17788 D_17788.
    stepST F_1778c D_1778c (Z_to_bv 64 0x51bb8) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_17790 D_17790 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_17794 D_17794 (Z_to_bv 64 0x51bc8).
    stepn F_17798 D_17798.
    stepn F_1779c D_1779c.
    stepLD8 F_177a0 D_177a0 (Z_to_bv 64 0x178c8).
    stepLD8 F_177a4 D_177a4 (Z_to_bv 64 0x13d30).
    (* [comment removed for export] *)
    stepn F_177a8 D_177a8. rewrite Hs0.
    stepn F_177ac D_177ac.
    stepLW F_1f5e0 D_1f5e0 0%Z.
    stepb_ft F_1f5e4 D_1f5e4 ltac:(cond_compute).
    stepretL F_1f5e8 D_1f5e8 (0x177b0 : word).
    (* [comment removed for export] *)
    stepn F_177b0 D_177b0.
    stepretL F_177b4 D_177b4 (0x178c8 : word).
    stepretL F_178c8 D_178c8 (0x13d30 : word).
    (* [comment removed for export] *)
    stepn F_13d30 D_13d30.
    stepLBU F_13d34 D_13d34 (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_13d38 D_13d38 ltac:(cond_compute).
    stepretL F_13d3c D_13d3c (0x177b8 : word).
    (* [comment removed for export] *)
    stepn F_177b8 D_177b8.
    stepn F_177bc D_177bc.
    stepn F_1f358 D_1f358.
    stepLB0 F_1f35c D_1f35c.
    stepb_tk F_1f360 D_1f360 ltac:(cond_compute).
    stepretL F_1f550 D_1f550 (0x177c0 : word).
    (* [comment removed for export] *)
    stepLW F_177c0 D_177c0 0%Z.
    stepn F_177c4 D_177c4.
    stepST F_177c8 D_177c8 (Z_to_bv 64 0x51bb8) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_177cc D_177cc ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_177d0 D_177d0 (Z_to_bv 64 0x51bc8).
    stepn F_177d4 D_177d4.
    stepLD8 F_17774 D_17774 (Z_to_bv 64 0).
    stepn F_17778 D_17778.
    stepST F_1777c D_1777c (Z_to_bv 64 0x51bb8) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_17780 D_17780 (Z_to_bv 64 0x51bc0) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_17784 D_17784 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_177d8 D_177d8.
    stepST F_177dc D_177dc (Z_to_bv 64 0x51bb0) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_177e0 D_177e0.
    (* [comment removed for export] *)
    stepLD8 F_177e4 D_177e4 (Z_to_bv 64 0x17980).
    stepLD8 F_177e8 D_177e8 code.
    stepLD8 F_177ec D_177ec s1v.
    stepLD8 F_177f0 D_177f0 s2v.
    stepLD8 F_177f4 D_177f4 s3v.
    stepn F_177f8 D_177f8. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_177fc D_177fc.
    stepLW F_1f5e0 D_1f5e0 0%Z.
    stepb_ft F_1f5e4 D_1f5e4 ltac:(cond_compute).
    stepretL F_1f5e8 D_1f5e8 (0x17980 : word).
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
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x17984)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x17900)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x20730)))
    (Z_to_bv 64 0x21a68) [Z_to_bv 8 1].

Section V2R.
  Context {fx : FPState}.
Lemma w2R : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x207d8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x20738)) ->
  rdn RSEGS mem (Z_to_bv 64 0x207e0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x20730)) ->
  rdn RSEGS mem (Z_to_bv 64 0x20730) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13878)) ->
  rdn RSEGS mem (Z_to_bv 64 0x21a68) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x20778) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x17800)) ->
  rdn RSEGS mem (Z_to_bv 64 0x20780) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x217e8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x217e8)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x17980 : word) mem rom)
                 (mkst regs' (0x19ae4 : word) (mem_w2R mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x17988.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mg2 Mdso.
  unfold mem_w2R. eexists. split.
  - (* [comment removed for export] *)
    stepn F_17980 D_17980.
    stepn F_178d0 D_178d0. rewrite Hsp. sp_renorm.
    stepST F_178d4 D_178d4 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x17984) ltac:(sok_stack SOK).
    stepST F_178d8 D_178d8 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_178dc D_178dc (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_178e0 D_178e0.
    stepn F_178e4 D_178e4.
    stepLD8 F_178e8 D_178e8 (Z_to_bv 64 0x20738).
    stepLD8 F_178ec D_178ec (Z_to_bv 64 0x20730).
    (* [comment removed for export] *)
    stepb_ft F_178f0 D_178f0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_178f4 D_178f4 (Z_to_bv 64 0x13878).
    stepn F_178f8 D_178f8.
    stepretL F_178fc D_178fc (0x13878 : word).
    (* [comment removed for export] *)
    stepn F_13878 D_13878. sp_renorm.
    stepST F_1387c D_1387c (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x17900) ltac:(sok_stack SOK).
    stepST F_13880 D_13880 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x20730) ltac:(sok_stack SOK).
    stepn F_13884 D_13884.
    stepn F_13888 D_13888.
    stepn F_1388c D_1388c.
    (* [comment removed for export] *)
    stepLBU F_13890 D_13890 (Z_to_bv 8 0) ltac:(rewrite ?v_addi_0; rdn_by Mcomp).
    stepn F_13894 D_13894.
    stepb_tk F_13898 D_13898 ltac:(cond_compute).
    stepn F_138a4 D_138a4.
    stepn F_138a8 D_138a8.
    stepn F_138ac D_138ac.
    (* [comment removed for export] *)
    stepST F_138b0 D_138b0 (Z_to_bv 64 0x21a68) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_138b4 D_138b4.
    stepLD8 F_138b8 D_138b8 (Z_to_bv 64 0x17800).
    stepb_ft F_138bc D_138bc ltac:(cond_compute).
    stepn F_138c0 D_138c0.
    stepn F_138c4 D_138c4.
    stepn F_138c8 D_138c8.
    stepLD8 F_138cc D_138cc (Z_to_bv 64 0x217e8).
    stepn F_138d0 D_138d0.
    stepretL F_17800 D_17800 (0x138d4 : word).
    stepn F_138d4 D_138d4.
    (* [comment removed for export] *)
    stepn F_138d8 D_138d8.
    stepLD8 F_138dc D_138dc (Z_to_bv 64 0).
    stepb_tk F_138e0 D_138e0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_138f8 D_138f8 (Z_to_bv 64 0x17900).
    stepLD8 F_138fc D_138fc (Z_to_bv 64 0x20730).
    stepn F_13900 D_13900. sp_renorm.
    stepretL F_13904 D_13904 (0x17900 : word).
    (* [comment removed for export] *)
    stepn F_17900 D_17900.
    stepb_ft F_17904 D_17904 ltac:(cond_compute).
    stepLD8 F_17908 D_17908 (Z_to_bv 64 0x17984).
    stepLD8 F_1790c D_1790c code.
    stepLD8 F_17910 D_17910 s1v.
    stepn F_17914 D_17914. sp_renorm.
    (* [comment removed for export] *)
    stepn F_17918 D_17918.
    stepretL F_178cc D_178cc (0x17984 : word).
    stepn F_17984 D_17984.
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
    msteps RSEGS (mkst regs (0x1791c : word) mem rom) (mkst regs' (0x19ae4 : word) mem' rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x17988
    /\ store_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true
    /\ (forall (a : Z) n bs, rdn RSEGS mem (Z_to_bv 64 a) n = Some bs ->
          (0 <= a)%Z -> (a + Z.of_nat n <= 0x53000)%Z ->
          (a + Z.of_nat n <= 0x21a68 \/ 0x21a69 <= a)%Z ->
          (a + Z.of_nat n <= 0x51bb0 \/ 0x51bc8 <= a)%Z ->
          (a + Z.of_nat n <= 0x51dd0 \/ 0x51dd4 <= a)%Z ->
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
  file_clean mem 0x21920 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0x1791c : word) mem (seg_rom RSEGS)) model)
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
  assert (FC1 : file_clean mem1 0x21920 wp1 rp1).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (FC2 : file_clean mem1 0x21830 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_clean fx v8_reloc v8_code v8_sites v8_data v8_rw
             regs1 mem1 model sp code wp1 rp1 wp2 rp2 Rsp Rs0 Rra Esplo Esphi SOK1 G1 FC1 FC2 Hh Hlazy).
Qed.
End VP1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stdout_pending_G : forall mem wb wp bufp bufsz rp1 can pending,
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  @StdioDefs.stdout_pending v8_reloc mem wb wp bufp bufsz rp1 can pending.
Proof.
  intros mem wb wp bufp bufsz rp1 can pending [f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14].
  exact (@StdioDefs.Build_stdout_pending v8_reloc mem wb wp bufp bufsz rp1 can pending
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
  realizes RSEGS (mkCfg (mkst regs (0x1791c : word) mem (seg_rom RSEGS)) model)
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
  assert (FC2 : file_clean mem1 0x21830 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (SP1 : stdout_pending mem1 wb wp bufp bufsz rp1 can pending).
  { constructor; zaddr_goal; try assumption.
    1-9: (apply TR; [assumption | cbn; lia ..]).
    - apply TR; [assumption | lia ..].
    - split; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_flush fx v8_reloc v8_code v8_sites v8_data v8_rw
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
  realizes RSEGS (mkCfg (mkst regs (0x1791c : word) mem (seg_rom RSEGS)) model)
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
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x1791c) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending PRE.
  replace (Z_to_bv 64 0x1791c) with (0x1791c : word) by (apply bv_eq; reflexivity).
  exact (ref_exit regs mem model code pending PRE).
Qed.
End VP5.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End V8Exit.
