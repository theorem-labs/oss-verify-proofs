(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.kernel_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver Require Import LibWritevG.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import LibAtomic.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc Require Import Reloc RelocKit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl Require Import MuslTac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl Require StdioDefs Exit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17 Require Import V17Kit V17_code_exitpath.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module V17Exit.
Import V17Kit.V17ExitBase.
Import V17Kit.V17StdioDefs.
Import V17Kit.V17Reloc.
Import V17Kit.V17RelocCode.
Import V17Kit.V17RelocSites.
Import V17Kit.V17RelocImg.
Import V17Kit.V17RelocMusl.

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
    (Z_to_bv 64 0x51000) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x16bac)))
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
  rdn RSEGS mem (Z_to_bv 64 0x51000) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5102b) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x16b48 : word) mem rom)
                 (mkst regs' (0x16990 : word)
                       (mem_wA mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 64)
    /\ getr regs' 8 = Z_to_bv 64 0x50de4
    /\ getr regs' 18 = Z_to_bv 64 0x50de0.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl.
  unfold mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepn F_16b48 D_16b48. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_16b4c D_16b4c (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_16b50 D_16b50 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_16b54 D_16b54.
    stepn F_16b58 D_16b58. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_16b5c D_16b5c (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_16b60 D_16b60.
    stepn F_16b64 D_16b64.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_16b68 | reflexivity | exact D_16b68
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_16b6c | reflexivity | exact D_16b6c | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_16b70 | reflexivity | exact D_16b70
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_16b74 D_16b74 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_16b78 D_16b78.
    (* [comment removed for export] *)
    stepb_ft F_16b7c D_16b7c ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_16b80 D_16b80 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_16ba4 D_16ba4. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_16ba8 D_16ba8.
    (* [comment removed for export] *)
    stepn F_16964 D_16964. sp_renorm.
    stepST F_16968 D_16968 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x16bac) ltac:(sok_stack SOK).
    stepST F_1696c D_1696c (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_16970 D_16970 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_16974 D_16974 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_16978 D_16978 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_1697c D_1697c.
    stepn F_16980 D_16980.
    stepn F_16984 D_16984.
    stepn F_16988 D_16988.
    stepn F_1698c D_1698c.
    (* [comment removed for export] *)
    stepn F_1e584 D_1e584.
    stepLB0 F_1e588 D_1e588.
    stepb_tk F_1e58c D_1e58c ltac:(cond_compute).
    stepretL F_1e77c D_1e77c (0x16990 : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wN (m : word -> option byte) := wbytes m (Z_to_bv 64 0x50de0) [Z_to_bv 8 1].

Section VN.
  Context {fx : FPState}.
Lemma wN : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x50de4 -> getr regs 18 = Z_to_bv 64 0x50de0 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x50df0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x50de4) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x16990 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0x16bac : word) (mem_wN (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Malock.
  unfold mem_wN, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_16990 D_16990 (Z_to_bv 64 0).
    stepb_tk F_16994 D_16994 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_16a04 D_16a04.
    stepST F_16a08 D_16a08 (Z_to_bv 64 0x50de0) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_16a0c D_16a0c. rewrite Hs0.
    (* [comment removed for export] *)
    stepLD8 F_16a10 D_16a10 (Z_to_bv 64 0x16bac).
    stepLD8 F_16a14 D_16a14 code.
    stepLD8 F_16a18 D_16a18 s1v.
    stepLD8 F_16a1c D_16a1c s2v.
    stepLD8 F_16a20 D_16a20 s3v.
    stepn F_16a24 D_16a24. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_16a28 D_16a28.
    stepLW F_1e80c D_1e80c 0%Z.
    stepb_ft F_1e810 D_1e810 ltac:(cond_compute).
    stepretL F_1e814 D_1e814 (0x16bac : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wO (m : word -> option byte) :=
  wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 0x50de8) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x50de8) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0x50de8) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x50df0) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x50de0) [Z_to_bv 8 1].

Section VO.
  Context {fx : FPState}.
Lemma wO : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x50de4 -> getr regs 18 = Z_to_bv 64 0x50de0 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x50df0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x50df8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x50de8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
  rdn RSEGS mem (Z_to_bv 64 0x50df8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x50e00) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x16af4)) ->
  rdn RSEGS mem (Z_to_bv 64 0x50f00) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x139e0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x30ca4) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x50de4) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5102b) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x16990 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0x16bac : word) (mem_wO (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Mslot Mnext Mf0 Ma0 Mcb Malock Mnl.
  unfold mem_wO, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_16990 D_16990 (Z_to_bv 64 0x50df8).
    stepb_ft F_16994 D_16994 ltac:(cond_compute).
    stepLW F_16998 D_16998 1%Z.
    stepn F_1699c D_1699c.
    (* [comment removed for export] *)
    stepn F_169b4 D_169b4.
    stepST F_169b8 D_169b8 (Z_to_bv 64 0x50de8) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_169bc D_169bc ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_169c0 D_169c0 (Z_to_bv 64 0x50df8).
    stepn F_169c4 D_169c4.
    stepn F_169c8 D_169c8.
    stepLD8 F_169cc D_169cc (Z_to_bv 64 0x16af4).
    stepLD8 F_169d0 D_169d0 (Z_to_bv 64 0x139e0).
    (* [comment removed for export] *)
    stepn F_169d4 D_169d4. rewrite Hs0.
    stepn F_169d8 D_169d8.
    stepLW F_1e80c D_1e80c 0%Z.
    stepb_ft F_1e810 D_1e810 ltac:(cond_compute).
    stepretL F_1e814 D_1e814 (0x169dc : word).
    (* [comment removed for export] *)
    stepn F_169dc D_169dc.
    stepretL F_169e0 D_169e0 (0x16af4 : word).
    stepretL F_16af4 D_16af4 (0x139e0 : word).
    (* [comment removed for export] *)
    stepn F_139e0 D_139e0.
    stepLBU F_139e4 D_139e4 (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_139e8 D_139e8 ltac:(cond_compute).
    stepretL F_139ec D_139ec (0x169e4 : word).
    (* [comment removed for export] *)
    stepn F_169e4 D_169e4.
    stepn F_169e8 D_169e8.
    stepn F_1e584 D_1e584.
    stepLB0 F_1e588 D_1e588.
    stepb_tk F_1e58c D_1e58c ltac:(cond_compute).
    stepretL F_1e77c D_1e77c (0x169ec : word).
    (* [comment removed for export] *)
    stepLW F_169ec D_169ec 0%Z.
    stepn F_169f0 D_169f0.
    stepST F_169f4 D_169f4 (Z_to_bv 64 0x50de8) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_169f8 D_169f8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_169fc D_169fc (Z_to_bv 64 0x50df8).
    stepn F_16a00 D_16a00.
    stepLD8 F_169a0 D_169a0 (Z_to_bv 64 0).
    stepn F_169a4 D_169a4.
    stepST F_169a8 D_169a8 (Z_to_bv 64 0x50de8) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_169ac D_169ac (Z_to_bv 64 0x50df0) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_169b0 D_169b0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_16a04 D_16a04.
    stepST F_16a08 D_16a08 (Z_to_bv 64 0x50de0) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_16a0c D_16a0c.
    (* [comment removed for export] *)
    stepLD8 F_16a10 D_16a10 (Z_to_bv 64 0x16bac).
    stepLD8 F_16a14 D_16a14 code.
    stepLD8 F_16a18 D_16a18 s1v.
    stepLD8 F_16a1c D_16a1c s2v.
    stepLD8 F_16a20 D_16a20 s3v.
    stepn F_16a24 D_16a24. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_16a28 D_16a28.
    stepLW F_1e80c D_1e80c 0%Z.
    stepb_ft F_1e810 D_1e810 ltac:(cond_compute).
    stepretL F_1e814 D_1e814 (0x16bac : word).
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
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x16bb0)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x16b2c)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x1f960)))
    (Z_to_bv 64 0x20c98) [Z_to_bv 8 1].

Section V2R.
  Context {fx : FPState}.
Lemma w2R : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x1fa08) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1f968)) ->
  rdn RSEGS mem (Z_to_bv 64 0x1fa10) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1f960)) ->
  rdn RSEGS mem (Z_to_bv 64 0x1f960) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13528)) ->
  rdn RSEGS mem (Z_to_bv 64 0x20c98) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x1f9a8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x16a2c)) ->
  rdn RSEGS mem (Z_to_bv 64 0x1f9b0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x20a18) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x20a18)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x16bac : word) mem rom)
                 (mkst regs' (0x18d10 : word) (mem_w2R mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x16bb4.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mg2 Mdso.
  unfold mem_w2R. eexists. split.
  - (* [comment removed for export] *)
    stepn F_16bac D_16bac.
    stepn F_16afc D_16afc. rewrite Hsp. sp_renorm.
    stepST F_16b00 D_16b00 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x16bb0) ltac:(sok_stack SOK).
    stepST F_16b04 D_16b04 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_16b08 D_16b08 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_16b0c D_16b0c.
    stepn F_16b10 D_16b10.
    stepLD8 F_16b14 D_16b14 (Z_to_bv 64 0x1f968).
    stepLD8 F_16b18 D_16b18 (Z_to_bv 64 0x1f960).
    (* [comment removed for export] *)
    stepb_ft F_16b1c D_16b1c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_16b20 D_16b20 (Z_to_bv 64 0x13528).
    stepn F_16b24 D_16b24.
    stepretL F_16b28 D_16b28 (0x13528 : word).
    (* [comment removed for export] *)
    stepn F_13528 D_13528. sp_renorm.
    stepST F_1352c D_1352c (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x16b2c) ltac:(sok_stack SOK).
    stepST F_13530 D_13530 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x1f960) ltac:(sok_stack SOK).
    stepn F_13534 D_13534.
    stepn F_13538 D_13538.
    stepn F_1353c D_1353c.
    (* [comment removed for export] *)
    stepLBU F_13540 D_13540 (Z_to_bv 8 0) ltac:(rewrite ?v_addi_0; rdn_by Mcomp).
    stepn F_13544 D_13544.
    stepb_tk F_13548 D_13548 ltac:(cond_compute).
    stepn F_13554 D_13554.
    stepn F_13558 D_13558.
    stepn F_1355c D_1355c.
    (* [comment removed for export] *)
    stepST F_13560 D_13560 (Z_to_bv 64 0x20c98) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_13564 D_13564.
    stepLD8 F_13568 D_13568 (Z_to_bv 64 0x16a2c).
    stepb_ft F_1356c D_1356c ltac:(cond_compute).
    stepn F_13570 D_13570.
    stepn F_13574 D_13574.
    stepn F_13578 D_13578.
    stepLD8 F_1357c D_1357c (Z_to_bv 64 0x20a18).
    stepn F_13580 D_13580.
    stepretL F_16a2c D_16a2c (0x13584 : word).
    stepn F_13584 D_13584.
    (* [comment removed for export] *)
    stepn F_13588 D_13588.
    stepLD8 F_1358c D_1358c (Z_to_bv 64 0).
    stepb_tk F_13590 D_13590 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_135a8 D_135a8 (Z_to_bv 64 0x16b2c).
    stepLD8 F_135ac D_135ac (Z_to_bv 64 0x1f960).
    stepn F_135b0 D_135b0. sp_renorm.
    stepretL F_135b4 D_135b4 (0x16b2c : word).
    (* [comment removed for export] *)
    stepn F_16b2c D_16b2c.
    stepb_ft F_16b30 D_16b30 ltac:(cond_compute).
    stepLD8 F_16b34 D_16b34 (Z_to_bv 64 0x16bb0).
    stepLD8 F_16b38 D_16b38 code.
    stepLD8 F_16b3c D_16b3c s1v.
    stepn F_16b40 D_16b40. sp_renorm.
    (* [comment removed for export] *)
    stepn F_16b44 D_16b44.
    stepretL F_16af8 D_16af8 (0x16bb0 : word).
    stepn F_16bb0 D_16bb0.
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
    msteps RSEGS (mkst regs (0x16b48 : word) mem rom) (mkst regs' (0x18d10 : word) mem' rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x16bb4
    /\ store_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true
    /\ (forall (a : Z) n bs, rdn RSEGS mem (Z_to_bv 64 a) n = Some bs ->
          (0 <= a)%Z -> (a + Z.of_nat n <= 0x52000)%Z ->
          (a + Z.of_nat n <= 0x20c98 \/ 0x20c99 <= a)%Z ->
          (a + Z.of_nat n <= 0x50de0 \/ 0x50df8 <= a)%Z ->
          (a + Z.of_nat n <= 0x51000 \/ 0x51004 <= a)%Z ->
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
  file_clean mem 0x20b50 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0x16b48 : word) mem (seg_rom RSEGS)) model)
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
  assert (FC1 : file_clean mem1 0x20b50 wp1 rp1).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (FC2 : file_clean mem1 0x20a60 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_clean fx v17_reloc v17_code v17_sites v17_data v17_rw
             regs1 mem1 model sp code wp1 rp1 wp2 rp2 Rsp Rs0 Rra Esplo Esphi SOK1 G1 FC1 FC2 Hh Hlazy).
Qed.
End VP1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stdout_pending_G : forall mem wb wp bufp bufsz rp1 can pending,
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  @StdioDefs.stdout_pending v17_reloc mem wb wp bufp bufsz rp1 can pending.
Proof.
  intros mem wb wp bufp bufsz rp1 can pending [f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14].
  exact (@StdioDefs.Build_stdout_pending v17_reloc mem wb wp bufp bufsz rp1 can pending
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
  realizes RSEGS (mkCfg (mkst regs (0x16b48 : word) mem (seg_rom RSEGS)) model)
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
  assert (FC2 : file_clean mem1 0x20a60 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (SP1 : stdout_pending mem1 wb wp bufp bufsz rp1 can pending).
  { constructor; zaddr_goal; try assumption.
    1-9: (apply TR; [assumption | cbn; lia ..]).
    - apply TR; [assumption | lia ..].
    - split; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_flush fx v17_reloc v17_code v17_sites v17_data v17_rw
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
  realizes RSEGS (mkCfg (mkst regs (0x16b48 : word) mem (seg_rom RSEGS)) model)
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
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x16b48) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending PRE.
  replace (Z_to_bv 64 0x16b48) with (0x16b48 : word) by (apply bv_eq; reflexivity).
  exact (ref_exit regs mem model code pending PRE).
Qed.
End VP5.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End V17Exit.
