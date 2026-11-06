(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix1_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.CliDriver Require Import LibWritevG.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica Require Import LibAtomic.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Reloc Require Import Reloc RelocKit.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Musl Require Import MuslTac.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Musl Require StdioDefs Exit.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.V22 Require Import V22Kit V22_code_exitpath.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module V22Exit.
Import V22Kit.V22ExitBase.
Import V22Kit.V22StdioDefs.
Import V22Kit.V22Reloc.
Import V22Kit.V22RelocCode.
Import V22Kit.V22RelocSites.
Import V22Kit.V22RelocImg.
Import V22Kit.V22RelocMusl.

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
    (Z_to_bv 64 0x50470) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x16024)))
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
  rdn RSEGS mem (Z_to_bv 64 0x50470) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5049b) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x15fc0 : word) mem rom)
                 (mkst regs' (0x15e08 : word)
                       (mem_wA mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 64)
    /\ getr regs' 8 = Z_to_bv 64 0x50254
    /\ getr regs' 18 = Z_to_bv 64 0x50250.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl.
  unfold mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepn F_15fc0 D_15fc0. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_15fc4 D_15fc4 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_15fc8 D_15fc8 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_15fcc D_15fcc.
    stepn F_15fd0 D_15fd0. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_15fd4 D_15fd4 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_15fd8 D_15fd8.
    stepn F_15fdc D_15fdc.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_15fe0 | reflexivity | exact D_15fe0
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_15fe4 | reflexivity | exact D_15fe4 | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_15fe8 | reflexivity | exact D_15fe8
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_15fec D_15fec ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_15ff0 D_15ff0.
    (* [comment removed for export] *)
    stepb_ft F_15ff4 D_15ff4 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_15ff8 D_15ff8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_1601c D_1601c. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_16020 D_16020.
    (* [comment removed for export] *)
    stepn F_15ddc D_15ddc. sp_renorm.
    stepST F_15de0 D_15de0 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x16024) ltac:(sok_stack SOK).
    stepST F_15de4 D_15de4 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_15de8 D_15de8 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_15dec D_15dec (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_15df0 D_15df0 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_15df4 D_15df4.
    stepn F_15df8 D_15df8.
    stepn F_15dfc D_15dfc.
    stepn F_15e00 D_15e00.
    stepn F_15e04 D_15e04.
    (* [comment removed for export] *)
    stepn F_1d9fc D_1d9fc.
    stepLB0 F_1da00 D_1da00.
    stepb_tk F_1da04 D_1da04 ltac:(cond_compute).
    stepretL F_1dbf4 D_1dbf4 (0x15e08 : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wN (m : word -> option byte) := wbytes m (Z_to_bv 64 0x50250) [Z_to_bv 8 1].

Section VN.
  Context {fx : FPState}.
Lemma wN : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x50254 -> getr regs 18 = Z_to_bv 64 0x50250 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x50260) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x50254) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x15e08 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0x16024 : word) (mem_wN (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Malock.
  unfold mem_wN, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_15e08 D_15e08 (Z_to_bv 64 0).
    stepb_tk F_15e0c D_15e0c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_15e7c D_15e7c.
    stepST F_15e80 D_15e80 (Z_to_bv 64 0x50250) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_15e84 D_15e84. rewrite Hs0.
    (* [comment removed for export] *)
    stepLD8 F_15e88 D_15e88 (Z_to_bv 64 0x16024).
    stepLD8 F_15e8c D_15e8c code.
    stepLD8 F_15e90 D_15e90 s1v.
    stepLD8 F_15e94 D_15e94 s2v.
    stepLD8 F_15e98 D_15e98 s3v.
    stepn F_15e9c D_15e9c. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_15ea0 D_15ea0.
    stepLW F_1dc84 D_1dc84 0%Z.
    stepb_ft F_1dc88 D_1dc88 ltac:(cond_compute).
    stepretL F_1dc8c D_1dc8c (0x16024 : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wO (m : word -> option byte) :=
  wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 0x50258) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x50258) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0x50258) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x50260) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x50250) [Z_to_bv 8 1].

Section VO.
  Context {fx : FPState}.
Lemma wO : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x50254 -> getr regs 18 = Z_to_bv 64 0x50250 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x50260) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x50268)) ->
  rdn RSEGS mem (Z_to_bv 64 0x50258) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
  rdn RSEGS mem (Z_to_bv 64 0x50268) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x50270) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x15f6c)) ->
  rdn RSEGS mem (Z_to_bv 64 0x50370) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x136cc)) ->
  rdn RSEGS mem (Z_to_bv 64 0x30114) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x50254) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5049b) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x15e08 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0x16024 : word) (mem_wO (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Mslot Mnext Mf0 Ma0 Mcb Malock Mnl.
  unfold mem_wO, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_15e08 D_15e08 (Z_to_bv 64 0x50268).
    stepb_ft F_15e0c D_15e0c ltac:(cond_compute).
    stepLW F_15e10 D_15e10 1%Z.
    stepn F_15e14 D_15e14.
    (* [comment removed for export] *)
    stepn F_15e2c D_15e2c.
    stepST F_15e30 D_15e30 (Z_to_bv 64 0x50258) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_15e34 D_15e34 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_15e38 D_15e38 (Z_to_bv 64 0x50268).
    stepn F_15e3c D_15e3c.
    stepn F_15e40 D_15e40.
    stepLD8 F_15e44 D_15e44 (Z_to_bv 64 0x15f6c).
    stepLD8 F_15e48 D_15e48 (Z_to_bv 64 0x136cc).
    (* [comment removed for export] *)
    stepn F_15e4c D_15e4c. rewrite Hs0.
    stepn F_15e50 D_15e50.
    stepLW F_1dc84 D_1dc84 0%Z.
    stepb_ft F_1dc88 D_1dc88 ltac:(cond_compute).
    stepretL F_1dc8c D_1dc8c (0x15e54 : word).
    (* [comment removed for export] *)
    stepn F_15e54 D_15e54.
    stepretL F_15e58 D_15e58 (0x15f6c : word).
    stepretL F_15f6c D_15f6c (0x136cc : word).
    (* [comment removed for export] *)
    stepn F_136cc D_136cc.
    stepLBU F_136d0 D_136d0 (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_136d4 D_136d4 ltac:(cond_compute).
    stepretL F_136d8 D_136d8 (0x15e5c : word).
    (* [comment removed for export] *)
    stepn F_15e5c D_15e5c.
    stepn F_15e60 D_15e60.
    stepn F_1d9fc D_1d9fc.
    stepLB0 F_1da00 D_1da00.
    stepb_tk F_1da04 D_1da04 ltac:(cond_compute).
    stepretL F_1dbf4 D_1dbf4 (0x15e64 : word).
    (* [comment removed for export] *)
    stepLW F_15e64 D_15e64 0%Z.
    stepn F_15e68 D_15e68.
    stepST F_15e6c D_15e6c (Z_to_bv 64 0x50258) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_15e70 D_15e70 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_15e74 D_15e74 (Z_to_bv 64 0x50268).
    stepn F_15e78 D_15e78.
    stepLD8 F_15e18 D_15e18 (Z_to_bv 64 0).
    stepn F_15e1c D_15e1c.
    stepST F_15e20 D_15e20 (Z_to_bv 64 0x50258) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_15e24 D_15e24 (Z_to_bv 64 0x50260) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_15e28 D_15e28 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_15e7c D_15e7c.
    stepST F_15e80 D_15e80 (Z_to_bv 64 0x50250) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_15e84 D_15e84.
    (* [comment removed for export] *)
    stepLD8 F_15e88 D_15e88 (Z_to_bv 64 0x16024).
    stepLD8 F_15e8c D_15e8c code.
    stepLD8 F_15e90 D_15e90 s1v.
    stepLD8 F_15e94 D_15e94 s2v.
    stepLD8 F_15e98 D_15e98 s3v.
    stepn F_15e9c D_15e9c. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_15ea0 D_15ea0.
    stepLW F_1dc84 D_1dc84 0%Z.
    stepb_ft F_1dc88 D_1dc88 ltac:(cond_compute).
    stepretL F_1dc8c D_1dc8c (0x16024 : word).
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
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x16028)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x15fa4)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x1edd8)))
    (Z_to_bv 64 0x20108) [Z_to_bv 8 1].

Section V2R.
  Context {fx : FPState}.
Lemma w2R : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x1ee80) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1ede0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x1ee88) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1edd8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x1edd8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13214)) ->
  rdn RSEGS mem (Z_to_bv 64 0x20108) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x1ee20) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x15ea4)) ->
  rdn RSEGS mem (Z_to_bv 64 0x1ee28) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x1fe90) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1fe90)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x16024 : word) mem rom)
                 (mkst regs' (0x18188 : word) (mem_w2R mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x1602c.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mg2 Mdso.
  unfold mem_w2R. eexists. split.
  - (* [comment removed for export] *)
    stepn F_16024 D_16024.
    stepn F_15f74 D_15f74. rewrite Hsp. sp_renorm.
    stepST F_15f78 D_15f78 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x16028) ltac:(sok_stack SOK).
    stepST F_15f7c D_15f7c (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_15f80 D_15f80 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_15f84 D_15f84.
    stepn F_15f88 D_15f88.
    stepLD8 F_15f8c D_15f8c (Z_to_bv 64 0x1ede0).
    stepLD8 F_15f90 D_15f90 (Z_to_bv 64 0x1edd8).
    (* [comment removed for export] *)
    stepb_ft F_15f94 D_15f94 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_15f98 D_15f98 (Z_to_bv 64 0x13214).
    stepn F_15f9c D_15f9c.
    stepretL F_15fa0 D_15fa0 (0x13214 : word).
    (* [comment removed for export] *)
    stepn F_13214 D_13214. sp_renorm.
    stepST F_13218 D_13218 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x15fa4) ltac:(sok_stack SOK).
    stepST F_1321c D_1321c (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x1edd8) ltac:(sok_stack SOK).
    stepn F_13220 D_13220.
    stepn F_13224 D_13224.
    stepn F_13228 D_13228.
    (* [comment removed for export] *)
    stepLBU F_1322c D_1322c (Z_to_bv 8 0) ltac:(rewrite ?v_addi_0; rdn_by Mcomp).
    stepn F_13230 D_13230.
    stepb_tk F_13234 D_13234 ltac:(cond_compute).
    stepn F_13240 D_13240.
    stepn F_13244 D_13244.
    stepn F_13248 D_13248.
    (* [comment removed for export] *)
    stepST F_1324c D_1324c (Z_to_bv 64 0x20108) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_13250 D_13250.
    stepLD8 F_13254 D_13254 (Z_to_bv 64 0x15ea4).
    stepb_ft F_13258 D_13258 ltac:(cond_compute).
    stepn F_1325c D_1325c.
    stepn F_13260 D_13260.
    stepn F_13264 D_13264.
    stepLD8 F_13268 D_13268 (Z_to_bv 64 0x1fe90).
    stepn F_1326c D_1326c.
    stepretL F_15ea4 D_15ea4 (0x13270 : word).
    stepn F_13270 D_13270.
    (* [comment removed for export] *)
    stepn F_13274 D_13274.
    stepLD8 F_13278 D_13278 (Z_to_bv 64 0).
    stepb_tk F_1327c D_1327c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_13294 D_13294 (Z_to_bv 64 0x15fa4).
    stepLD8 F_13298 D_13298 (Z_to_bv 64 0x1edd8).
    stepn F_1329c D_1329c. sp_renorm.
    stepretL F_132a0 D_132a0 (0x15fa4 : word).
    (* [comment removed for export] *)
    stepn F_15fa4 D_15fa4.
    stepb_ft F_15fa8 D_15fa8 ltac:(cond_compute).
    stepLD8 F_15fac D_15fac (Z_to_bv 64 0x16028).
    stepLD8 F_15fb0 D_15fb0 code.
    stepLD8 F_15fb4 D_15fb4 s1v.
    stepn F_15fb8 D_15fb8. sp_renorm.
    (* [comment removed for export] *)
    stepn F_15fbc D_15fbc.
    stepretL F_15f70 D_15f70 (0x16028 : word).
    stepn F_16028 D_16028.
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
    msteps RSEGS (mkst regs (0x15fc0 : word) mem rom) (mkst regs' (0x18188 : word) mem' rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x1602c
    /\ store_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true
    /\ (forall (a : Z) n bs, rdn RSEGS mem (Z_to_bv 64 a) n = Some bs ->
          (0 <= a)%Z -> (a + Z.of_nat n <= 0x51000)%Z ->
          (a + Z.of_nat n <= 0x20108 \/ 0x20109 <= a)%Z ->
          (a + Z.of_nat n <= 0x50250 \/ 0x50268 <= a)%Z ->
          (a + Z.of_nat n <= 0x50470 \/ 0x50474 <= a)%Z ->
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
  file_clean mem 0x1ffc8 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0x15fc0 : word) mem (seg_rom RSEGS)) model)
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
  assert (FC1 : file_clean mem1 0x1ffc8 wp1 rp1).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (FC2 : file_clean mem1 0x1fed8 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_clean fx v22_reloc v22_code v22_sites v22_data v22_rw
             regs1 mem1 model sp code wp1 rp1 wp2 rp2 Rsp Rs0 Rra Esplo Esphi SOK1 G1 FC1 FC2 Hh Hlazy).
Qed.
End VP1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stdout_pending_G : forall mem wb wp bufp bufsz rp1 can pending,
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  @StdioDefs.stdout_pending v22_reloc mem wb wp bufp bufsz rp1 can pending.
Proof.
  intros mem wb wp bufp bufsz rp1 can pending [f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14].
  exact (@StdioDefs.Build_stdout_pending v22_reloc mem wb wp bufp bufsz rp1 can pending
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
  realizes RSEGS (mkCfg (mkst regs (0x15fc0 : word) mem (seg_rom RSEGS)) model)
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
  assert (FC2 : file_clean mem1 0x1fed8 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (SP1 : stdout_pending mem1 wb wp bufp bufsz rp1 can pending).
  { constructor; zaddr_goal; try assumption.
    1-9: (apply TR; [assumption | cbn; lia ..]).
    - apply TR; [assumption | lia ..].
    - split; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_flush fx v22_reloc v22_code v22_sites v22_data v22_rw
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
  realizes RSEGS (mkCfg (mkst regs (0x15fc0 : word) mem (seg_rom RSEGS)) model)
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
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x15fc0) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending PRE.
  replace (Z_to_bv 64 0x15fc0) with (0x15fc0 : word) by (apply bv_eq; reflexivity).
  exact (ref_exit regs mem model code pending PRE).
Qed.
End VP5.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End V22Exit.
