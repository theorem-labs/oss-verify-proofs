(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver Require Import LibWritevG.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import LibAtomic.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require Import Reloc RelocKit.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require Import MuslTac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require StdioDefs Exit.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14Kit O14_code_exitpath.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module O14Exit.
Import O14Kit.O14ExitBase.
Import O14Kit.O14StdioDefs.
Import O14Kit.O14Reloc.
Import O14Kit.O14RelocCode.
Import O14Kit.O14RelocSites.
Import O14Kit.O14RelocImg.
Import O14Kit.O14RelocMusl.

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
    (Z_to_bv 64 0x5c070) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x21c20)))
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
  rdn RSEGS mem (Z_to_bv 64 0x5c070) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5c09b) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x21bbc : word) mem rom)
                 (mkst regs' (0x21a04 : word)
                       (mem_wA mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 64)
    /\ getr regs' 8 = Z_to_bv 64 0x5be54
    /\ getr regs' 18 = Z_to_bv 64 0x5be50.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl.
  unfold mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepn F_21bbc D_21bbc. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_21bc0 D_21bc0 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_21bc4 D_21bc4 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_21bc8 D_21bc8.
    stepn F_21bcc D_21bcc. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_21bd0 D_21bd0 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_21bd4 D_21bd4.
    stepn F_21bd8 D_21bd8.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_21bdc | reflexivity | exact D_21bdc
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_21be0 | reflexivity | exact D_21be0 | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_21be4 | reflexivity | exact D_21be4
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_21be8 D_21be8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_21bec D_21bec.
    (* [comment removed for export] *)
    stepb_ft F_21bf0 D_21bf0 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_21bf4 D_21bf4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_21c18 D_21c18. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_21c1c D_21c1c.
    (* [comment removed for export] *)
    stepn F_219d8 D_219d8. sp_renorm.
    stepST F_219dc D_219dc (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x21c20) ltac:(sok_stack SOK).
    stepST F_219e0 D_219e0 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_219e4 D_219e4 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_219e8 D_219e8 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_219ec D_219ec (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_219f0 D_219f0.
    stepn F_219f4 D_219f4.
    stepn F_219f8 D_219f8.
    stepn F_219fc D_219fc.
    stepn F_21a00 D_21a00.
    (* [comment removed for export] *)
    stepn F_295f8 D_295f8.
    stepLB0 F_295fc D_295fc.
    stepb_tk F_29600 D_29600 ltac:(cond_compute).
    stepretL F_297f0 D_297f0 (0x21a04 : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wN (m : word -> option byte) := wbytes m (Z_to_bv 64 0x5be50) [Z_to_bv 8 1].

Section VN.
  Context {fx : FPState}.
Lemma wN : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x5be54 -> getr regs 18 = Z_to_bv 64 0x5be50 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x5be60) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5be54) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x21a04 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0x21c20 : word) (mem_wN (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Malock.
  unfold mem_wN, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_21a04 D_21a04 (Z_to_bv 64 0).
    stepb_tk F_21a08 D_21a08 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_21a78 D_21a78.
    stepST F_21a7c D_21a7c (Z_to_bv 64 0x5be50) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_21a80 D_21a80. rewrite Hs0.
    (* [comment removed for export] *)
    stepLD8 F_21a84 D_21a84 (Z_to_bv 64 0x21c20).
    stepLD8 F_21a88 D_21a88 code.
    stepLD8 F_21a8c D_21a8c s1v.
    stepLD8 F_21a90 D_21a90 s2v.
    stepLD8 F_21a94 D_21a94 s3v.
    stepn F_21a98 D_21a98. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_21a9c D_21a9c.
    stepLW F_29880 D_29880 0%Z.
    stepb_ft F_29884 D_29884 ltac:(cond_compute).
    stepretL F_29888 D_29888 (0x21c20 : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wO (m : word -> option byte) :=
  wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 0x5be58) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x5be58) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0x5be58) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x5be60) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x5be50) [Z_to_bv 8 1].

Section VO.
  Context {fx : FPState}.
Lemma wO : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x5be54 -> getr regs 18 = Z_to_bv 64 0x5be50 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x5be60) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x5be68)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5be58) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5be68) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5be70) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x21b68)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5bf70) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x151cc)) ->
  rdn RSEGS mem (Z_to_bv 64 0x3bd14) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x5be54) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5c09b) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x21a04 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0x21c20 : word) (mem_wO (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Mslot Mnext Mf0 Ma0 Mcb Malock Mnl.
  unfold mem_wO, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_21a04 D_21a04 (Z_to_bv 64 0x5be68).
    stepb_ft F_21a08 D_21a08 ltac:(cond_compute).
    stepLW F_21a0c D_21a0c 1%Z.
    stepn F_21a10 D_21a10.
    (* [comment removed for export] *)
    stepn F_21a28 D_21a28.
    stepST F_21a2c D_21a2c (Z_to_bv 64 0x5be58) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_21a30 D_21a30 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_21a34 D_21a34 (Z_to_bv 64 0x5be68).
    stepn F_21a38 D_21a38.
    stepn F_21a3c D_21a3c.
    stepLD8 F_21a40 D_21a40 (Z_to_bv 64 0x21b68).
    stepLD8 F_21a44 D_21a44 (Z_to_bv 64 0x151cc).
    (* [comment removed for export] *)
    stepn F_21a48 D_21a48. rewrite Hs0.
    stepn F_21a4c D_21a4c.
    stepLW F_29880 D_29880 0%Z.
    stepb_ft F_29884 D_29884 ltac:(cond_compute).
    stepretL F_29888 D_29888 (0x21a50 : word).
    (* [comment removed for export] *)
    stepn F_21a50 D_21a50.
    stepretL F_21a54 D_21a54 (0x21b68 : word).
    stepretL F_21b68 D_21b68 (0x151cc : word).
    (* [comment removed for export] *)
    stepn F_151cc D_151cc.
    stepLBU F_151d0 D_151d0 (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_151d4 D_151d4 ltac:(cond_compute).
    stepretL F_151d8 D_151d8 (0x21a58 : word).
    (* [comment removed for export] *)
    stepn F_21a58 D_21a58.
    stepn F_21a5c D_21a5c.
    stepn F_295f8 D_295f8.
    stepLB0 F_295fc D_295fc.
    stepb_tk F_29600 D_29600 ltac:(cond_compute).
    stepretL F_297f0 D_297f0 (0x21a60 : word).
    (* [comment removed for export] *)
    stepLW F_21a60 D_21a60 0%Z.
    stepn F_21a64 D_21a64.
    stepST F_21a68 D_21a68 (Z_to_bv 64 0x5be58) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_21a6c D_21a6c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_21a70 D_21a70 (Z_to_bv 64 0x5be68).
    stepn F_21a74 D_21a74.
    stepLD8 F_21a14 D_21a14 (Z_to_bv 64 0).
    stepn F_21a18 D_21a18.
    stepST F_21a1c D_21a1c (Z_to_bv 64 0x5be58) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_21a20 D_21a20 (Z_to_bv 64 0x5be60) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_21a24 D_21a24 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_21a78 D_21a78.
    stepST F_21a7c D_21a7c (Z_to_bv 64 0x5be50) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_21a80 D_21a80.
    (* [comment removed for export] *)
    stepLD8 F_21a84 D_21a84 (Z_to_bv 64 0x21c20).
    stepLD8 F_21a88 D_21a88 code.
    stepLD8 F_21a8c D_21a8c s1v.
    stepLD8 F_21a90 D_21a90 s2v.
    stepLD8 F_21a94 D_21a94 s3v.
    stepn F_21a98 D_21a98. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_21a9c D_21a9c.
    stepLW F_29880 D_29880 0%Z.
    stepb_ft F_29884 D_29884 ltac:(cond_compute).
    stepretL F_29888 D_29888 (0x21c20 : word).
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
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x21c24)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x21ba0)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x2a9d0)))
    (Z_to_bv 64 0x2bd08) [Z_to_bv 8 1].

Section V2R.
  Context {fx : FPState}.
Lemma w2R : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x2aa78) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2a9d8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x2aa80) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2a9d0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x2a9d0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x14d14)) ->
  rdn RSEGS mem (Z_to_bv 64 0x2bd08) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x2aa18) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x21aa0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x2aa20) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x2ba88) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2ba88)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x21c20 : word) mem rom)
                 (mkst regs' (0x23d84 : word) (mem_w2R mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x21c28.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mg2 Mdso.
  unfold mem_w2R. eexists. split.
  - (* [comment removed for export] *)
    stepn F_21c20 D_21c20.
    stepn F_21b70 D_21b70. rewrite Hsp. sp_renorm.
    stepST F_21b74 D_21b74 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x21c24) ltac:(sok_stack SOK).
    stepST F_21b78 D_21b78 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_21b7c D_21b7c (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_21b80 D_21b80.
    stepn F_21b84 D_21b84.
    stepLD8 F_21b88 D_21b88 (Z_to_bv 64 0x2a9d8).
    stepLD8 F_21b8c D_21b8c (Z_to_bv 64 0x2a9d0).
    (* [comment removed for export] *)
    stepb_ft F_21b90 D_21b90 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_21b94 D_21b94 (Z_to_bv 64 0x14d14).
    stepn F_21b98 D_21b98.
    stepretL F_21b9c D_21b9c (0x14d14 : word).
    (* [comment removed for export] *)
    stepn F_14d14 D_14d14. sp_renorm.
    stepST F_14d18 D_14d18 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x21ba0) ltac:(sok_stack SOK).
    stepST F_14d1c D_14d1c (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x2a9d0) ltac:(sok_stack SOK).
    stepn F_14d20 D_14d20.
    stepn F_14d24 D_14d24.
    stepn F_14d28 D_14d28.
    (* [comment removed for export] *)
    stepLBU F_14d2c D_14d2c (Z_to_bv 8 0) ltac:(rewrite ?v_addi_0; rdn_by Mcomp).
    stepn F_14d30 D_14d30.
    stepb_tk F_14d34 D_14d34 ltac:(cond_compute).
    stepn F_14d40 D_14d40.
    stepn F_14d44 D_14d44.
    stepn F_14d48 D_14d48.
    (* [comment removed for export] *)
    stepST F_14d4c D_14d4c (Z_to_bv 64 0x2bd08) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_14d50 D_14d50.
    stepLD8 F_14d54 D_14d54 (Z_to_bv 64 0x21aa0).
    stepb_ft F_14d58 D_14d58 ltac:(cond_compute).
    stepn F_14d5c D_14d5c.
    stepn F_14d60 D_14d60.
    stepn F_14d64 D_14d64.
    stepLD8 F_14d68 D_14d68 (Z_to_bv 64 0x2ba88).
    stepn F_14d6c D_14d6c.
    stepretL F_21aa0 D_21aa0 (0x14d70 : word).
    stepn F_14d70 D_14d70.
    (* [comment removed for export] *)
    stepn F_14d74 D_14d74.
    stepLD8 F_14d78 D_14d78 (Z_to_bv 64 0).
    stepb_tk F_14d7c D_14d7c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_14d94 D_14d94 (Z_to_bv 64 0x21ba0).
    stepLD8 F_14d98 D_14d98 (Z_to_bv 64 0x2a9d0).
    stepn F_14d9c D_14d9c. sp_renorm.
    stepretL F_14da0 D_14da0 (0x21ba0 : word).
    (* [comment removed for export] *)
    stepn F_21ba0 D_21ba0.
    stepb_ft F_21ba4 D_21ba4 ltac:(cond_compute).
    stepLD8 F_21ba8 D_21ba8 (Z_to_bv 64 0x21c24).
    stepLD8 F_21bac D_21bac code.
    stepLD8 F_21bb0 D_21bb0 s1v.
    stepn F_21bb4 D_21bb4. sp_renorm.
    (* [comment removed for export] *)
    stepn F_21bb8 D_21bb8.
    stepretL F_21b6c D_21b6c (0x21c24 : word).
    stepn F_21c24 D_21c24.
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
    msteps RSEGS (mkst regs (0x21bbc : word) mem rom) (mkst regs' (0x23d84 : word) mem' rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x21c28
    /\ store_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true
    /\ (forall (a : Z) n bs, rdn RSEGS mem (Z_to_bv 64 a) n = Some bs ->
          (0 <= a)%Z -> (a + Z.of_nat n <= 0x5d000)%Z ->
          (a + Z.of_nat n <= 0x2bd08 \/ 0x2bd09 <= a)%Z ->
          (a + Z.of_nat n <= 0x5be50 \/ 0x5be68 <= a)%Z ->
          (a + Z.of_nat n <= 0x5c070 \/ 0x5c074 <= a)%Z ->
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
  file_clean mem 0x2bbc0 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0x21bbc : word) mem (seg_rom RSEGS)) model)
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
  assert (FC1 : file_clean mem1 0x2bbc0 wp1 rp1).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (FC2 : file_clean mem1 0x2bad0 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_clean fx o14_reloc o14_code o14_sites o14_data o14_rw
             regs1 mem1 model sp code wp1 rp1 wp2 rp2 Rsp Rs0 Rra Esplo Esphi SOK1 G1 FC1 FC2 Hh Hlazy).
Qed.
End VP1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stdout_pending_G : forall mem wb wp bufp bufsz rp1 can pending,
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  @StdioDefs.stdout_pending o14_reloc mem wb wp bufp bufsz rp1 can pending.
Proof.
  intros mem wb wp bufp bufsz rp1 can pending [f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14].
  exact (@StdioDefs.Build_stdout_pending o14_reloc mem wb wp bufp bufsz rp1 can pending
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
  realizes RSEGS (mkCfg (mkst regs (0x21bbc : word) mem (seg_rom RSEGS)) model)
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
  assert (FC2 : file_clean mem1 0x2bad0 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (SP1 : stdout_pending mem1 wb wp bufp bufsz rp1 can pending).
  { constructor; zaddr_goal; try assumption.
    1-9: (apply TR; [assumption | cbn; lia ..]).
    - apply TR; [assumption | lia ..].
    - split; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_flush fx o14_reloc o14_code o14_sites o14_data o14_rw
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
  realizes RSEGS (mkCfg (mkst regs (0x21bbc : word) mem (seg_rom RSEGS)) model)
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
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x21bbc) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending PRE.
  replace (Z_to_bv 64 0x21bbc) with (0x21bbc : word) by (apply bv_eq; reflexivity).
  exact (ref_exit regs mem model code pending PRE).
Qed.
End VP5.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End O14Exit.
