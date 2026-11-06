(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.paintcmap_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.CliDriver Require Import LibWritevG.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require Import LibAtomic.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Reloc Require Import Reloc RelocKit.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Musl Require Import MuslTac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Musl Require StdioDefs Exit.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.O21 Require Import O21Kit O21_code_exitpath.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module O21Exit.
Import O21Kit.O21ExitBase.
Import O21Kit.O21StdioDefs.
Import O21Kit.O21Reloc.
Import O21Kit.O21RelocCode.
Import O21Kit.O21RelocSites.
Import O21Kit.O21RelocImg.
Import O21Kit.O21RelocMusl.

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
    (Z_to_bv 64 0x51b50) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x176fc)))
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
  rdn RSEGS mem (Z_to_bv 64 0x51b50) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x51b7b) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x17698 : word) mem rom)
                 (mkst regs' (0x174e0 : word)
                       (mem_wA mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 64)
    /\ getr regs' 8 = Z_to_bv 64 0x51934
    /\ getr regs' 18 = Z_to_bv 64 0x51930.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl.
  unfold mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepn F_17698 D_17698. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_1769c D_1769c (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_176a0 D_176a0 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_176a4 D_176a4.
    stepn F_176a8 D_176a8. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_176ac D_176ac (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_176b0 D_176b0.
    stepn F_176b4 D_176b4.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_176b8 | reflexivity | exact D_176b8
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_176bc | reflexivity | exact D_176bc | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_176c0 | reflexivity | exact D_176c0
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_176c4 D_176c4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_176c8 D_176c8.
    (* [comment removed for export] *)
    stepb_ft F_176cc D_176cc ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_176d0 D_176d0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_176f4 D_176f4. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_176f8 D_176f8.
    (* [comment removed for export] *)
    stepn F_174b4 D_174b4. sp_renorm.
    stepST F_174b8 D_174b8 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x176fc) ltac:(sok_stack SOK).
    stepST F_174bc D_174bc (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_174c0 D_174c0 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_174c4 D_174c4 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_174c8 D_174c8 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_174cc D_174cc.
    stepn F_174d0 D_174d0.
    stepn F_174d4 D_174d4.
    stepn F_174d8 D_174d8.
    stepn F_174dc D_174dc.
    (* [comment removed for export] *)
    stepn F_1f0d4 D_1f0d4.
    stepLB0 F_1f0d8 D_1f0d8.
    stepb_tk F_1f0dc D_1f0dc ltac:(cond_compute).
    stepretL F_1f2cc D_1f2cc (0x174e0 : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wN (m : word -> option byte) := wbytes m (Z_to_bv 64 0x51930) [Z_to_bv 8 1].

Section VN.
  Context {fx : FPState}.
Lemma wN : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x51934 -> getr regs 18 = Z_to_bv 64 0x51930 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x51940) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x51934) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x174e0 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0x176fc : word) (mem_wN (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Malock.
  unfold mem_wN, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_174e0 D_174e0 (Z_to_bv 64 0).
    stepb_tk F_174e4 D_174e4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_17554 D_17554.
    stepST F_17558 D_17558 (Z_to_bv 64 0x51930) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_1755c D_1755c. rewrite Hs0.
    (* [comment removed for export] *)
    stepLD8 F_17560 D_17560 (Z_to_bv 64 0x176fc).
    stepLD8 F_17564 D_17564 code.
    stepLD8 F_17568 D_17568 s1v.
    stepLD8 F_1756c D_1756c s2v.
    stepLD8 F_17570 D_17570 s3v.
    stepn F_17574 D_17574. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_17578 D_17578.
    stepLW F_1f35c D_1f35c 0%Z.
    stepb_ft F_1f360 D_1f360 ltac:(cond_compute).
    stepretL F_1f364 D_1f364 (0x176fc : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wO (m : word -> option byte) :=
  wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 0x51938) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x51938) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0x51938) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x51940) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x51930) [Z_to_bv 8 1].

Section VO.
  Context {fx : FPState}.
Lemma wO : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x51934 -> getr regs 18 = Z_to_bv 64 0x51930 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x51940) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x51948)) ->
  rdn RSEGS mem (Z_to_bv 64 0x51938) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
  rdn RSEGS mem (Z_to_bv 64 0x51948) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x51950) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x17644)) ->
  rdn RSEGS mem (Z_to_bv 64 0x51a50) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13c48)) ->
  rdn RSEGS mem (Z_to_bv 64 0x317f4) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x51934) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x51b7b) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x174e0 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0x176fc : word) (mem_wO (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Mslot Mnext Mf0 Ma0 Mcb Malock Mnl.
  unfold mem_wO, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_174e0 D_174e0 (Z_to_bv 64 0x51948).
    stepb_ft F_174e4 D_174e4 ltac:(cond_compute).
    stepLW F_174e8 D_174e8 1%Z.
    stepn F_174ec D_174ec.
    (* [comment removed for export] *)
    stepn F_17504 D_17504.
    stepST F_17508 D_17508 (Z_to_bv 64 0x51938) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_1750c D_1750c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_17510 D_17510 (Z_to_bv 64 0x51948).
    stepn F_17514 D_17514.
    stepn F_17518 D_17518.
    stepLD8 F_1751c D_1751c (Z_to_bv 64 0x17644).
    stepLD8 F_17520 D_17520 (Z_to_bv 64 0x13c48).
    (* [comment removed for export] *)
    stepn F_17524 D_17524. rewrite Hs0.
    stepn F_17528 D_17528.
    stepLW F_1f35c D_1f35c 0%Z.
    stepb_ft F_1f360 D_1f360 ltac:(cond_compute).
    stepretL F_1f364 D_1f364 (0x1752c : word).
    (* [comment removed for export] *)
    stepn F_1752c D_1752c.
    stepretL F_17530 D_17530 (0x17644 : word).
    stepretL F_17644 D_17644 (0x13c48 : word).
    (* [comment removed for export] *)
    stepn F_13c48 D_13c48.
    stepLBU F_13c4c D_13c4c (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_13c50 D_13c50 ltac:(cond_compute).
    stepretL F_13c54 D_13c54 (0x17534 : word).
    (* [comment removed for export] *)
    stepn F_17534 D_17534.
    stepn F_17538 D_17538.
    stepn F_1f0d4 D_1f0d4.
    stepLB0 F_1f0d8 D_1f0d8.
    stepb_tk F_1f0dc D_1f0dc ltac:(cond_compute).
    stepretL F_1f2cc D_1f2cc (0x1753c : word).
    (* [comment removed for export] *)
    stepLW F_1753c D_1753c 0%Z.
    stepn F_17540 D_17540.
    stepST F_17544 D_17544 (Z_to_bv 64 0x51938) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_17548 D_17548 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_1754c D_1754c (Z_to_bv 64 0x51948).
    stepn F_17550 D_17550.
    stepLD8 F_174f0 D_174f0 (Z_to_bv 64 0).
    stepn F_174f4 D_174f4.
    stepST F_174f8 D_174f8 (Z_to_bv 64 0x51938) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_174fc D_174fc (Z_to_bv 64 0x51940) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_17500 D_17500 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_17554 D_17554.
    stepST F_17558 D_17558 (Z_to_bv 64 0x51930) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_1755c D_1755c.
    (* [comment removed for export] *)
    stepLD8 F_17560 D_17560 (Z_to_bv 64 0x176fc).
    stepLD8 F_17564 D_17564 code.
    stepLD8 F_17568 D_17568 s1v.
    stepLD8 F_1756c D_1756c s2v.
    stepLD8 F_17570 D_17570 s3v.
    stepn F_17574 D_17574. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_17578 D_17578.
    stepLW F_1f35c D_1f35c 0%Z.
    stepb_ft F_1f360 D_1f360 ltac:(cond_compute).
    stepretL F_1f364 D_1f364 (0x176fc : word).
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
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x17700)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x1767c)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x204b0)))
    (Z_to_bv 64 0x217e8) [Z_to_bv 8 1].

Section V2R.
  Context {fx : FPState}.
Lemma w2R : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x20558) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x204b8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x20560) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x204b0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x204b0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13790)) ->
  rdn RSEGS mem (Z_to_bv 64 0x217e8) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x204f8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1757c)) ->
  rdn RSEGS mem (Z_to_bv 64 0x20500) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x21568) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x21568)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x176fc : word) mem rom)
                 (mkst regs' (0x19860 : word) (mem_w2R mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x17704.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mg2 Mdso.
  unfold mem_w2R. eexists. split.
  - (* [comment removed for export] *)
    stepn F_176fc D_176fc.
    stepn F_1764c D_1764c. rewrite Hsp. sp_renorm.
    stepST F_17650 D_17650 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x17700) ltac:(sok_stack SOK).
    stepST F_17654 D_17654 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_17658 D_17658 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_1765c D_1765c.
    stepn F_17660 D_17660.
    stepLD8 F_17664 D_17664 (Z_to_bv 64 0x204b8).
    stepLD8 F_17668 D_17668 (Z_to_bv 64 0x204b0).
    (* [comment removed for export] *)
    stepb_ft F_1766c D_1766c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_17670 D_17670 (Z_to_bv 64 0x13790).
    stepn F_17674 D_17674.
    stepretL F_17678 D_17678 (0x13790 : word).
    (* [comment removed for export] *)
    stepn F_13790 D_13790. sp_renorm.
    stepST F_13794 D_13794 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x1767c) ltac:(sok_stack SOK).
    stepST F_13798 D_13798 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x204b0) ltac:(sok_stack SOK).
    stepn F_1379c D_1379c.
    stepn F_137a0 D_137a0.
    stepn F_137a4 D_137a4.
    (* [comment removed for export] *)
    stepLBU F_137a8 D_137a8 (Z_to_bv 8 0) ltac:(rewrite ?v_addi_0; rdn_by Mcomp).
    stepn F_137ac D_137ac.
    stepb_tk F_137b0 D_137b0 ltac:(cond_compute).
    stepn F_137bc D_137bc.
    stepn F_137c0 D_137c0.
    stepn F_137c4 D_137c4.
    (* [comment removed for export] *)
    stepST F_137c8 D_137c8 (Z_to_bv 64 0x217e8) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_137cc D_137cc.
    stepLD8 F_137d0 D_137d0 (Z_to_bv 64 0x1757c).
    stepb_ft F_137d4 D_137d4 ltac:(cond_compute).
    stepn F_137d8 D_137d8.
    stepn F_137dc D_137dc.
    stepn F_137e0 D_137e0.
    stepLD8 F_137e4 D_137e4 (Z_to_bv 64 0x21568).
    stepn F_137e8 D_137e8.
    stepretL F_1757c D_1757c (0x137ec : word).
    stepn F_137ec D_137ec.
    (* [comment removed for export] *)
    stepn F_137f0 D_137f0.
    stepLD8 F_137f4 D_137f4 (Z_to_bv 64 0).
    stepb_tk F_137f8 D_137f8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_13810 D_13810 (Z_to_bv 64 0x1767c).
    stepLD8 F_13814 D_13814 (Z_to_bv 64 0x204b0).
    stepn F_13818 D_13818. sp_renorm.
    stepretL F_1381c D_1381c (0x1767c : word).
    (* [comment removed for export] *)
    stepn F_1767c D_1767c.
    stepb_ft F_17680 D_17680 ltac:(cond_compute).
    stepLD8 F_17684 D_17684 (Z_to_bv 64 0x17700).
    stepLD8 F_17688 D_17688 code.
    stepLD8 F_1768c D_1768c s1v.
    stepn F_17690 D_17690. sp_renorm.
    (* [comment removed for export] *)
    stepn F_17694 D_17694.
    stepretL F_17648 D_17648 (0x17700 : word).
    stepn F_17700 D_17700.
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
    msteps RSEGS (mkst regs (0x17698 : word) mem rom) (mkst regs' (0x19860 : word) mem' rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x17704
    /\ store_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true
    /\ (forall (a : Z) n bs, rdn RSEGS mem (Z_to_bv 64 a) n = Some bs ->
          (0 <= a)%Z -> (a + Z.of_nat n <= 0x53000)%Z ->
          (a + Z.of_nat n <= 0x217e8 \/ 0x217e9 <= a)%Z ->
          (a + Z.of_nat n <= 0x51930 \/ 0x51948 <= a)%Z ->
          (a + Z.of_nat n <= 0x51b50 \/ 0x51b54 <= a)%Z ->
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
  file_clean mem 0x216a0 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0x17698 : word) mem (seg_rom RSEGS)) model)
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
  assert (FC1 : file_clean mem1 0x216a0 wp1 rp1).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (FC2 : file_clean mem1 0x215b0 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_clean fx o21_reloc o21_code o21_sites o21_data o21_rw
             regs1 mem1 model sp code wp1 rp1 wp2 rp2 Rsp Rs0 Rra Esplo Esphi SOK1 G1 FC1 FC2 Hh Hlazy).
Qed.
End VP1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stdout_pending_G : forall mem wb wp bufp bufsz rp1 can pending,
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  @StdioDefs.stdout_pending o21_reloc mem wb wp bufp bufsz rp1 can pending.
Proof.
  intros mem wb wp bufp bufsz rp1 can pending [f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14].
  exact (@StdioDefs.Build_stdout_pending o21_reloc mem wb wp bufp bufsz rp1 can pending
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
  realizes RSEGS (mkCfg (mkst regs (0x17698 : word) mem (seg_rom RSEGS)) model)
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
  assert (FC2 : file_clean mem1 0x215b0 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (SP1 : stdout_pending mem1 wb wp bufp bufsz rp1 can pending).
  { constructor; zaddr_goal; try assumption.
    1-9: (apply TR; [assumption | cbn; lia ..]).
    - apply TR; [assumption | lia ..].
    - split; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_flush fx o21_reloc o21_code o21_sites o21_data o21_rw
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
  realizes RSEGS (mkCfg (mkst regs (0x17698 : word) mem (seg_rom RSEGS)) model)
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
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x17698) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending PRE.
  replace (Z_to_bv 64 0x17698) with (0x17698 : word) by (apply bv_eq; reflexivity).
  exact (ref_exit regs mem model code pending PRE).
Qed.
End VP5.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End O21Exit.
