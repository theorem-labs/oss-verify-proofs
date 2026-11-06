(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.fhmtgen_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require Import LibWritevG.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import LibAtomic.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require Import Reloc RelocKit.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require Import MuslTac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require StdioDefs Exit.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.O10 Require Import O10Kit O10_code_exitpath.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module O10Exit.
Import O10Kit.O10ExitBase.
Import O10Kit.O10StdioDefs.
Import O10Kit.O10Reloc.
Import O10Kit.O10RelocCode.
Import O10Kit.O10RelocSites.
Import O10Kit.O10RelocImg.
Import O10Kit.O10RelocMusl.

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
    (Z_to_bv 64 0x5d360) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x22bc0)))
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
  rdn RSEGS mem (Z_to_bv 64 0x5d360) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5d38b) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x22b5c : word) mem rom)
                 (mkst regs' (0x229a4 : word)
                       (mem_wA mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 64)
    /\ getr regs' 8 = Z_to_bv 64 0x5d144
    /\ getr regs' 18 = Z_to_bv 64 0x5d140.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl.
  unfold mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepn F_22b5c D_22b5c. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_22b60 D_22b60 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_22b64 D_22b64 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_22b68 D_22b68.
    stepn F_22b6c D_22b6c. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_22b70 D_22b70 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_22b74 D_22b74.
    stepn F_22b78 D_22b78.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_22b7c | reflexivity | exact D_22b7c
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_22b80 | reflexivity | exact D_22b80 | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_22b84 | reflexivity | exact D_22b84
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_22b88 D_22b88 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_22b8c D_22b8c.
    (* [comment removed for export] *)
    stepb_ft F_22b90 D_22b90 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_22b94 D_22b94 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_22bb8 D_22bb8. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_22bbc D_22bbc.
    (* [comment removed for export] *)
    stepn F_22978 D_22978. sp_renorm.
    stepST F_2297c D_2297c (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x22bc0) ltac:(sok_stack SOK).
    stepST F_22980 D_22980 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_22984 D_22984 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_22988 D_22988 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_2298c D_2298c (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_22990 D_22990.
    stepn F_22994 D_22994.
    stepn F_22998 D_22998.
    stepn F_2299c D_2299c.
    stepn F_229a0 D_229a0.
    (* [comment removed for export] *)
    stepn F_2a5d0 D_2a5d0.
    stepLB0 F_2a5d4 D_2a5d4.
    stepb_tk F_2a5d8 D_2a5d8 ltac:(cond_compute).
    stepretL F_2a7c8 D_2a7c8 (0x229a4 : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wN (m : word -> option byte) := wbytes m (Z_to_bv 64 0x5d140) [Z_to_bv 8 1].

Section VN.
  Context {fx : FPState}.
Lemma wN : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x5d144 -> getr regs 18 = Z_to_bv 64 0x5d140 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x5d150) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5d144) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x229a4 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0x22bc0 : word) (mem_wN (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Malock.
  unfold mem_wN, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_229a4 D_229a4 (Z_to_bv 64 0).
    stepb_tk F_229a8 D_229a8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_22a18 D_22a18.
    stepST F_22a1c D_22a1c (Z_to_bv 64 0x5d140) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_22a20 D_22a20. rewrite Hs0.
    (* [comment removed for export] *)
    stepLD8 F_22a24 D_22a24 (Z_to_bv 64 0x22bc0).
    stepLD8 F_22a28 D_22a28 code.
    stepLD8 F_22a2c D_22a2c s1v.
    stepLD8 F_22a30 D_22a30 s2v.
    stepLD8 F_22a34 D_22a34 s3v.
    stepn F_22a38 D_22a38. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_22a3c D_22a3c.
    stepLW F_2a858 D_2a858 0%Z.
    stepb_ft F_2a85c D_2a85c ltac:(cond_compute).
    stepretL F_2a860 D_2a860 (0x22bc0 : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wO (m : word -> option byte) :=
  wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 0x5d148) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x5d148) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0x5d148) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x5d150) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x5d140) [Z_to_bv 8 1].

Section VO.
  Context {fx : FPState}.
Lemma wO : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x5d144 -> getr regs 18 = Z_to_bv 64 0x5d140 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x5d150) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x5d158)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5d148) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5d158) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5d160) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x22b08)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5d260) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x15504)) ->
  rdn RSEGS mem (Z_to_bv 64 0x3d004) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x5d144) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5d38b) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x229a4 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0x22bc0 : word) (mem_wO (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Mslot Mnext Mf0 Ma0 Mcb Malock Mnl.
  unfold mem_wO, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_229a4 D_229a4 (Z_to_bv 64 0x5d158).
    stepb_ft F_229a8 D_229a8 ltac:(cond_compute).
    stepLW F_229ac D_229ac 1%Z.
    stepn F_229b0 D_229b0.
    (* [comment removed for export] *)
    stepn F_229c8 D_229c8.
    stepST F_229cc D_229cc (Z_to_bv 64 0x5d148) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_229d0 D_229d0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_229d4 D_229d4 (Z_to_bv 64 0x5d158).
    stepn F_229d8 D_229d8.
    stepn F_229dc D_229dc.
    stepLD8 F_229e0 D_229e0 (Z_to_bv 64 0x22b08).
    stepLD8 F_229e4 D_229e4 (Z_to_bv 64 0x15504).
    (* [comment removed for export] *)
    stepn F_229e8 D_229e8. rewrite Hs0.
    stepn F_229ec D_229ec.
    stepLW F_2a858 D_2a858 0%Z.
    stepb_ft F_2a85c D_2a85c ltac:(cond_compute).
    stepretL F_2a860 D_2a860 (0x229f0 : word).
    (* [comment removed for export] *)
    stepn F_229f0 D_229f0.
    stepretL F_229f4 D_229f4 (0x22b08 : word).
    stepretL F_22b08 D_22b08 (0x15504 : word).
    (* [comment removed for export] *)
    stepn F_15504 D_15504.
    stepLBU F_15508 D_15508 (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_1550c D_1550c ltac:(cond_compute).
    stepretL F_15510 D_15510 (0x229f8 : word).
    (* [comment removed for export] *)
    stepn F_229f8 D_229f8.
    stepn F_229fc D_229fc.
    stepn F_2a5d0 D_2a5d0.
    stepLB0 F_2a5d4 D_2a5d4.
    stepb_tk F_2a5d8 D_2a5d8 ltac:(cond_compute).
    stepretL F_2a7c8 D_2a7c8 (0x22a00 : word).
    (* [comment removed for export] *)
    stepLW F_22a00 D_22a00 0%Z.
    stepn F_22a04 D_22a04.
    stepST F_22a08 D_22a08 (Z_to_bv 64 0x5d148) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_22a0c D_22a0c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_22a10 D_22a10 (Z_to_bv 64 0x5d158).
    stepn F_22a14 D_22a14.
    stepLD8 F_229b4 D_229b4 (Z_to_bv 64 0).
    stepn F_229b8 D_229b8.
    stepST F_229bc D_229bc (Z_to_bv 64 0x5d148) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_229c0 D_229c0 (Z_to_bv 64 0x5d150) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_229c4 D_229c4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_22a18 D_22a18.
    stepST F_22a1c D_22a1c (Z_to_bv 64 0x5d140) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_22a20 D_22a20.
    (* [comment removed for export] *)
    stepLD8 F_22a24 D_22a24 (Z_to_bv 64 0x22bc0).
    stepLD8 F_22a28 D_22a28 code.
    stepLD8 F_22a2c D_22a2c s1v.
    stepLD8 F_22a30 D_22a30 s2v.
    stepLD8 F_22a34 D_22a34 s3v.
    stepn F_22a38 D_22a38. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_22a3c D_22a3c.
    stepLW F_2a858 D_2a858 0%Z.
    stepb_ft F_2a85c D_2a85c ltac:(cond_compute).
    stepretL F_2a860 D_2a860 (0x22bc0 : word).
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
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x22bc4)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x22b40)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x2b9a8)))
    (Z_to_bv 64 0x2cff8) [Z_to_bv 8 1].

Section V2R.
  Context {fx : FPState}.
Lemma w2R : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x2ba50) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2b9b0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x2ba58) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2b9a8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x2b9a8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1504c)) ->
  rdn RSEGS mem (Z_to_bv 64 0x2cff8) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x2b9f0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x22a40)) ->
  rdn RSEGS mem (Z_to_bv 64 0x2b9f8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x2ca60) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2ca60)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x22bc0 : word) mem rom)
                 (mkst regs' (0x24d24 : word) (mem_w2R mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x22bc8.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mg2 Mdso.
  unfold mem_w2R. eexists. split.
  - (* [comment removed for export] *)
    stepn F_22bc0 D_22bc0.
    stepn F_22b10 D_22b10. rewrite Hsp. sp_renorm.
    stepST F_22b14 D_22b14 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x22bc4) ltac:(sok_stack SOK).
    stepST F_22b18 D_22b18 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_22b1c D_22b1c (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_22b20 D_22b20.
    stepn F_22b24 D_22b24.
    stepLD8 F_22b28 D_22b28 (Z_to_bv 64 0x2b9b0).
    stepLD8 F_22b2c D_22b2c (Z_to_bv 64 0x2b9a8).
    (* [comment removed for export] *)
    stepb_ft F_22b30 D_22b30 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_22b34 D_22b34 (Z_to_bv 64 0x1504c).
    stepn F_22b38 D_22b38.
    stepretL F_22b3c D_22b3c (0x1504c : word).
    (* [comment removed for export] *)
    stepn F_1504c D_1504c. sp_renorm.
    stepST F_15050 D_15050 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x22b40) ltac:(sok_stack SOK).
    stepST F_15054 D_15054 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x2b9a8) ltac:(sok_stack SOK).
    stepn F_15058 D_15058.
    stepn F_1505c D_1505c.
    stepn F_15060 D_15060.
    (* [comment removed for export] *)
    stepLBU F_15064 D_15064 (Z_to_bv 8 0) ltac:(rewrite ?v_addi_0; rdn_by Mcomp).
    stepn F_15068 D_15068.
    stepb_tk F_1506c D_1506c ltac:(cond_compute).
    stepn F_15078 D_15078.
    stepn F_1507c D_1507c.
    stepn F_15080 D_15080.
    (* [comment removed for export] *)
    stepST F_15084 D_15084 (Z_to_bv 64 0x2cff8) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_15088 D_15088.
    stepLD8 F_1508c D_1508c (Z_to_bv 64 0x22a40).
    stepb_ft F_15090 D_15090 ltac:(cond_compute).
    stepn F_15094 D_15094.
    stepn F_15098 D_15098.
    stepn F_1509c D_1509c.
    stepLD8 F_150a0 D_150a0 (Z_to_bv 64 0x2ca60).
    stepn F_150a4 D_150a4.
    stepretL F_22a40 D_22a40 (0x150a8 : word).
    stepn F_150a8 D_150a8.
    (* [comment removed for export] *)
    stepn F_150ac D_150ac.
    stepLD8 F_150b0 D_150b0 (Z_to_bv 64 0).
    stepb_tk F_150b4 D_150b4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_150cc D_150cc (Z_to_bv 64 0x22b40).
    stepLD8 F_150d0 D_150d0 (Z_to_bv 64 0x2b9a8).
    stepn F_150d4 D_150d4. sp_renorm.
    stepretL F_150d8 D_150d8 (0x22b40 : word).
    (* [comment removed for export] *)
    stepn F_22b40 D_22b40.
    stepb_ft F_22b44 D_22b44 ltac:(cond_compute).
    stepLD8 F_22b48 D_22b48 (Z_to_bv 64 0x22bc4).
    stepLD8 F_22b4c D_22b4c code.
    stepLD8 F_22b50 D_22b50 s1v.
    stepn F_22b54 D_22b54. sp_renorm.
    (* [comment removed for export] *)
    stepn F_22b58 D_22b58.
    stepretL F_22b0c D_22b0c (0x22bc4 : word).
    stepn F_22bc4 D_22bc4.
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
    msteps RSEGS (mkst regs (0x22b5c : word) mem rom) (mkst regs' (0x24d24 : word) mem' rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x22bc8
    /\ store_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true
    /\ (forall (a : Z) n bs, rdn RSEGS mem (Z_to_bv 64 a) n = Some bs ->
          (0 <= a)%Z -> (a + Z.of_nat n <= 0x5e000)%Z ->
          (a + Z.of_nat n <= 0x2cff8 \/ 0x2cff9 <= a)%Z ->
          (a + Z.of_nat n <= 0x5d140 \/ 0x5d158 <= a)%Z ->
          (a + Z.of_nat n <= 0x5d360 \/ 0x5d364 <= a)%Z ->
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
  file_clean mem 0x2ceb8 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0x22b5c : word) mem (seg_rom RSEGS)) model)
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
  assert (FC1 : file_clean mem1 0x2ceb8 wp1 rp1).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (FC2 : file_clean mem1 0x2cdc8 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_clean fx o10_reloc o10_code o10_sites o10_data o10_rw
             regs1 mem1 model sp code wp1 rp1 wp2 rp2 Rsp Rs0 Rra Esplo Esphi SOK1 G1 FC1 FC2 Hh Hlazy).
Qed.
End VP1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stdout_pending_G : forall mem wb wp bufp bufsz rp1 can pending,
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  @StdioDefs.stdout_pending o10_reloc mem wb wp bufp bufsz rp1 can pending.
Proof.
  intros mem wb wp bufp bufsz rp1 can pending [f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14].
  exact (@StdioDefs.Build_stdout_pending o10_reloc mem wb wp bufp bufsz rp1 can pending
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
  realizes RSEGS (mkCfg (mkst regs (0x22b5c : word) mem (seg_rom RSEGS)) model)
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
  assert (FC2 : file_clean mem1 0x2cdc8 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (SP1 : stdout_pending mem1 wb wp bufp bufsz rp1 can pending).
  { constructor; zaddr_goal; try assumption.
    1-9: (apply TR; [assumption | cbn; lia ..]).
    - apply TR; [assumption | lia ..].
    - split; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_flush fx o10_reloc o10_code o10_sites o10_data o10_rw
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
  realizes RSEGS (mkCfg (mkst regs (0x22b5c : word) mem (seg_rom RSEGS)) model)
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
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x22b5c) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending PRE.
  replace (Z_to_bv 64 0x22b5c) with (0x22b5c : word) by (apply bv_eq; reflexivity).
  exact (ref_exit regs mem model code pending PRE).
Qed.
End VP5.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End O10Exit.
