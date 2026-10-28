(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim ExitSim ShapeAlg Nodes.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require Import LibWritevG.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import LibAtomic.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require WalksLib.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require Import Spec.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require Import Reloc RelocKit.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require Import MuslTac.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require StdioDefs Exit.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10Kit V10_code_exitpath.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module V10Exit.
Import V10Kit.V10ExitBase.
Import V10Kit.V10StdioDefs.
Import V10Kit.V10Reloc.
Import V10Kit.V10RelocCode.
Import V10Kit.V10RelocSites.
Import V10Kit.V10RelocImg.
Import V10Kit.V10RelocMusl.

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
    (Z_to_bv 64 0x656e0) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x2af34)))
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
  rdn RSEGS mem (Z_to_bv 64 0x656e0) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x6570b) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x2aed0 : word) mem rom)
                 (mkst regs' (0x2ad18 : word)
                       (mem_wA mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 64)
    /\ getr regs' 8 = Z_to_bv 64 0x654c4
    /\ getr regs' 18 = Z_to_bv 64 0x654c0.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl.
  unfold mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepn F_2aed0 D_2aed0. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_2aed4 D_2aed4 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_2aed8 D_2aed8 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_2aedc D_2aedc.
    stepn F_2aee0 D_2aee0. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_2aee4 D_2aee4 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_2aee8 D_2aee8.
    stepn F_2aeec D_2aeec.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_2aef0 | reflexivity | exact D_2aef0
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_2aef4 | reflexivity | exact D_2aef4 | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_2aef8 | reflexivity | exact D_2aef8
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_2aefc D_2aefc ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_2af00 D_2af00.
    (* [comment removed for export] *)
    stepb_ft F_2af04 D_2af04 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_2af08 D_2af08 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_2af2c D_2af2c. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_2af30 D_2af30.
    (* [comment removed for export] *)
    stepn F_2acec D_2acec. sp_renorm.
    stepST F_2acf0 D_2acf0 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x2af34) ltac:(sok_stack SOK).
    stepST F_2acf4 D_2acf4 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_2acf8 D_2acf8 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_2acfc D_2acfc (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_2ad00 D_2ad00 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_2ad04 D_2ad04.
    stepn F_2ad08 D_2ad08.
    stepn F_2ad0c D_2ad0c.
    stepn F_2ad10 D_2ad10.
    stepn F_2ad14 D_2ad14.
    (* [comment removed for export] *)
    stepn F_32944 D_32944.
    stepLB0 F_32948 D_32948.
    stepb_tk F_3294c D_3294c ltac:(cond_compute).
    stepretL F_32b3c D_32b3c (0x2ad18 : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wN (m : word -> option byte) := wbytes m (Z_to_bv 64 0x654c0) [Z_to_bv 8 1].

Section VN.
  Context {fx : FPState}.
Lemma wN : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x654c4 -> getr regs 18 = Z_to_bv 64 0x654c0 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x654d0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x654c4) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x2ad18 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0x2af34 : word) (mem_wN (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Malock.
  unfold mem_wN, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_2ad18 D_2ad18 (Z_to_bv 64 0).
    stepb_tk F_2ad1c D_2ad1c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_2ad8c D_2ad8c.
    stepST F_2ad90 D_2ad90 (Z_to_bv 64 0x654c0) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_2ad94 D_2ad94. rewrite Hs0.
    (* [comment removed for export] *)
    stepLD8 F_2ad98 D_2ad98 (Z_to_bv 64 0x2af34).
    stepLD8 F_2ad9c D_2ad9c code.
    stepLD8 F_2ada0 D_2ada0 s1v.
    stepLD8 F_2ada4 D_2ada4 s2v.
    stepLD8 F_2ada8 D_2ada8 s3v.
    stepn F_2adac D_2adac. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_2adb0 D_2adb0.
    stepLW F_32bcc D_32bcc 0%Z.
    stepb_ft F_32bd0 D_32bd0 ltac:(cond_compute).
    stepretL F_32bd4 D_32bd4 (0x2af34 : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wO (m : word -> option byte) :=
  wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 0x654c8) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x654c8) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0x654c8) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x654d0) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x654c0) [Z_to_bv 8 1].

Section VO.
  Context {fx : FPState}.
Lemma wO : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x654c4 -> getr regs 18 = Z_to_bv 64 0x654c0 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x654d0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x654d8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x654c8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
  rdn RSEGS mem (Z_to_bv 64 0x654d8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x654e0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2ae7c)) ->
  rdn RSEGS mem (Z_to_bv 64 0x655e0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x15634)) ->
  rdn RSEGS mem (Z_to_bv 64 0x45384) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x654c4) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x6570b) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x2ad18 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0x2af34 : word) (mem_wO (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Mslot Mnext Mf0 Ma0 Mcb Malock Mnl.
  unfold mem_wO, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_2ad18 D_2ad18 (Z_to_bv 64 0x654d8).
    stepb_ft F_2ad1c D_2ad1c ltac:(cond_compute).
    stepLW F_2ad20 D_2ad20 1%Z.
    stepn F_2ad24 D_2ad24.
    (* [comment removed for export] *)
    stepn F_2ad3c D_2ad3c.
    stepST F_2ad40 D_2ad40 (Z_to_bv 64 0x654c8) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_2ad44 D_2ad44 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_2ad48 D_2ad48 (Z_to_bv 64 0x654d8).
    stepn F_2ad4c D_2ad4c.
    stepn F_2ad50 D_2ad50.
    stepLD8 F_2ad54 D_2ad54 (Z_to_bv 64 0x2ae7c).
    stepLD8 F_2ad58 D_2ad58 (Z_to_bv 64 0x15634).
    (* [comment removed for export] *)
    stepn F_2ad5c D_2ad5c. rewrite Hs0.
    stepn F_2ad60 D_2ad60.
    stepLW F_32bcc D_32bcc 0%Z.
    stepb_ft F_32bd0 D_32bd0 ltac:(cond_compute).
    stepretL F_32bd4 D_32bd4 (0x2ad64 : word).
    (* [comment removed for export] *)
    stepn F_2ad64 D_2ad64.
    stepretL F_2ad68 D_2ad68 (0x2ae7c : word).
    stepretL F_2ae7c D_2ae7c (0x15634 : word).
    (* [comment removed for export] *)
    stepn F_15634 D_15634.
    stepLBU F_15638 D_15638 (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_1563c D_1563c ltac:(cond_compute).
    stepretL F_15640 D_15640 (0x2ad6c : word).
    (* [comment removed for export] *)
    stepn F_2ad6c D_2ad6c.
    stepn F_2ad70 D_2ad70.
    stepn F_32944 D_32944.
    stepLB0 F_32948 D_32948.
    stepb_tk F_3294c D_3294c ltac:(cond_compute).
    stepretL F_32b3c D_32b3c (0x2ad74 : word).
    (* [comment removed for export] *)
    stepLW F_2ad74 D_2ad74 0%Z.
    stepn F_2ad78 D_2ad78.
    stepST F_2ad7c D_2ad7c (Z_to_bv 64 0x654c8) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_2ad80 D_2ad80 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_2ad84 D_2ad84 (Z_to_bv 64 0x654d8).
    stepn F_2ad88 D_2ad88.
    stepLD8 F_2ad28 D_2ad28 (Z_to_bv 64 0).
    stepn F_2ad2c D_2ad2c.
    stepST F_2ad30 D_2ad30 (Z_to_bv 64 0x654c8) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_2ad34 D_2ad34 (Z_to_bv 64 0x654d0) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_2ad38 D_2ad38 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_2ad8c D_2ad8c.
    stepST F_2ad90 D_2ad90 (Z_to_bv 64 0x654c0) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_2ad94 D_2ad94.
    (* [comment removed for export] *)
    stepLD8 F_2ad98 D_2ad98 (Z_to_bv 64 0x2af34).
    stepLD8 F_2ad9c D_2ad9c code.
    stepLD8 F_2ada0 D_2ada0 s1v.
    stepLD8 F_2ada4 D_2ada4 s2v.
    stepLD8 F_2ada8 D_2ada8 s3v.
    stepn F_2adac D_2adac. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_2adb0 D_2adb0.
    stepLW F_32bcc D_32bcc 0%Z.
    stepb_ft F_32bd0 D_32bd0 ltac:(cond_compute).
    stepretL F_32bd4 D_32bd4 (0x2af34 : word).
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
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x2af38)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x2aeb4)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x33d20)))
    (Z_to_bv 64 0x35378) [Z_to_bv 8 1].

Section V2R.
  Context {fx : FPState}.
Lemma w2R : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x33dc8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x33d28)) ->
  rdn RSEGS mem (Z_to_bv 64 0x33dd0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x33d20)) ->
  rdn RSEGS mem (Z_to_bv 64 0x33d20) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1517c)) ->
  rdn RSEGS mem (Z_to_bv 64 0x35378) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x33d68) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2adb4)) ->
  rdn RSEGS mem (Z_to_bv 64 0x33d70) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x34dd8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x34dd8)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x2af34 : word) mem rom)
                 (mkst regs' (0x2d098 : word) (mem_w2R mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x2af3c.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mg2 Mdso.
  unfold mem_w2R. eexists. split.
  - (* [comment removed for export] *)
    stepn F_2af34 D_2af34.
    stepn F_2ae84 D_2ae84. rewrite Hsp. sp_renorm.
    stepST F_2ae88 D_2ae88 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x2af38) ltac:(sok_stack SOK).
    stepST F_2ae8c D_2ae8c (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_2ae90 D_2ae90 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_2ae94 D_2ae94.
    stepn F_2ae98 D_2ae98.
    stepLD8 F_2ae9c D_2ae9c (Z_to_bv 64 0x33d28).
    stepLD8 F_2aea0 D_2aea0 (Z_to_bv 64 0x33d20).
    (* [comment removed for export] *)
    stepb_ft F_2aea4 D_2aea4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_2aea8 D_2aea8 (Z_to_bv 64 0x1517c).
    stepn F_2aeac D_2aeac.
    stepretL F_2aeb0 D_2aeb0 (0x1517c : word).
    (* [comment removed for export] *)
    stepn F_1517c D_1517c. sp_renorm.
    stepST F_15180 D_15180 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x2aeb4) ltac:(sok_stack SOK).
    stepST F_15184 D_15184 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x33d20) ltac:(sok_stack SOK).
    stepn F_15188 D_15188.
    stepn F_1518c D_1518c.
    stepn F_15190 D_15190.
    (* [comment removed for export] *)
    stepLBU F_15194 D_15194 (Z_to_bv 8 0) ltac:(rewrite ?v_addi_0; rdn_by Mcomp).
    stepn F_15198 D_15198.
    stepb_tk F_1519c D_1519c ltac:(cond_compute).
    stepn F_151a8 D_151a8.
    stepn F_151ac D_151ac.
    stepn F_151b0 D_151b0.
    (* [comment removed for export] *)
    stepST F_151b4 D_151b4 (Z_to_bv 64 0x35378) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_151b8 D_151b8.
    stepLD8 F_151bc D_151bc (Z_to_bv 64 0x2adb4).
    stepb_ft F_151c0 D_151c0 ltac:(cond_compute).
    stepn F_151c4 D_151c4.
    stepn F_151c8 D_151c8.
    stepn F_151cc D_151cc.
    stepLD8 F_151d0 D_151d0 (Z_to_bv 64 0x34dd8).
    stepn F_151d4 D_151d4.
    stepretL F_2adb4 D_2adb4 (0x151d8 : word).
    stepn F_151d8 D_151d8.
    (* [comment removed for export] *)
    stepn F_151dc D_151dc.
    stepLD8 F_151e0 D_151e0 (Z_to_bv 64 0).
    stepb_tk F_151e4 D_151e4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_151fc D_151fc (Z_to_bv 64 0x2aeb4).
    stepLD8 F_15200 D_15200 (Z_to_bv 64 0x33d20).
    stepn F_15204 D_15204. sp_renorm.
    stepretL F_15208 D_15208 (0x2aeb4 : word).
    (* [comment removed for export] *)
    stepn F_2aeb4 D_2aeb4.
    stepb_ft F_2aeb8 D_2aeb8 ltac:(cond_compute).
    stepLD8 F_2aebc D_2aebc (Z_to_bv 64 0x2af38).
    stepLD8 F_2aec0 D_2aec0 code.
    stepLD8 F_2aec4 D_2aec4 s1v.
    stepn F_2aec8 D_2aec8. sp_renorm.
    (* [comment removed for export] *)
    stepn F_2aecc D_2aecc.
    stepretL F_2ae80 D_2ae80 (0x2af38 : word).
    stepn F_2af38 D_2af38.
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
    msteps RSEGS (mkst regs (0x2aed0 : word) mem rom) (mkst regs' (0x2d098 : word) mem' rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x2af3c
    /\ store_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true
    /\ (forall (a : Z) n bs, rdn RSEGS mem (Z_to_bv 64 a) n = Some bs ->
          (0 <= a)%Z -> (a + Z.of_nat n <= 0x66000)%Z ->
          (a + Z.of_nat n <= 0x35378 \/ 0x35379 <= a)%Z ->
          (a + Z.of_nat n <= 0x654c0 \/ 0x654d8 <= a)%Z ->
          (a + Z.of_nat n <= 0x656e0 \/ 0x656e4 <= a)%Z ->
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
  file_clean mem 0x35230 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0x2aed0 : word) mem (seg_rom RSEGS)) model)
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
  assert (FC1 : file_clean mem1 0x35230 wp1 rp1).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (FC2 : file_clean mem1 0x35140 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_clean fx v10_reloc v10_code v10_sites v10_data v10_rw
             regs1 mem1 model sp code wp1 rp1 wp2 rp2 Rsp Rs0 Rra Esplo Esphi SOK1 G1 FC1 FC2 Hh Hlazy).
Qed.
End VP1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stdout_pending_G : forall mem wb wp bufp bufsz rp1 can pending,
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  @StdioDefs.stdout_pending v10_reloc mem wb wp bufp bufsz rp1 can pending.
Proof.
  intros mem wb wp bufp bufsz rp1 can pending [f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14].
  exact (@StdioDefs.Build_stdout_pending v10_reloc mem wb wp bufp bufsz rp1 can pending
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
  realizes RSEGS (mkCfg (mkst regs (0x2aed0 : word) mem (seg_rom RSEGS)) model)
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
  assert (FC2 : file_clean mem1 0x35140 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (SP1 : stdout_pending mem1 wb wp bufp bufsz rp1 can pending).
  { constructor; zaddr_goal; try assumption.
    1-9: (apply TR; [assumption | cbn; lia ..]).
    - apply TR; [assumption | lia ..].
    - split; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_flush fx v10_reloc v10_code v10_sites v10_data v10_rw
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
  realizes RSEGS (mkCfg (mkst regs (0x2aed0 : word) mem (seg_rom RSEGS)) model)
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
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2aed0) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending PRE.
  replace (Z_to_bv 64 0x2aed0) with (0x2aed0 : word) by (apply bv_eq; reflexivity).
  exact (ref_exit regs mem model code pending PRE).
Qed.
End VP5.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End V10Exit.
