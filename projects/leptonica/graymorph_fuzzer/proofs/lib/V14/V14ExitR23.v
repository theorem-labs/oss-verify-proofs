(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver Require Import LibWritevG.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import LibAtomic.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require Import Reloc RelocKit.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require Import MuslTac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require StdioDefs Exit.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.V14 Require Import V14Kit V14_code_exitpath.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module V14Exit.
Import V14Kit.V14ExitBase.
Import V14Kit.V14StdioDefs.
Import V14Kit.V14Reloc.
Import V14Kit.V14RelocCode.
Import V14Kit.V14RelocSites.
Import V14Kit.V14RelocImg.
Import V14Kit.V14RelocMusl.

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
    (Z_to_bv 64 0x643a0) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x29f4c)))
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
  rdn RSEGS mem (Z_to_bv 64 0x643a0) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x643cb) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x29ee8 : word) mem rom)
                 (mkst regs' (0x29d30 : word)
                       (mem_wA mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 64)
    /\ getr regs' 8 = Z_to_bv 64 0x64184
    /\ getr regs' 18 = Z_to_bv 64 0x64180.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl.
  unfold mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepn F_29ee8 D_29ee8. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_29eec D_29eec (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_29ef0 D_29ef0 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_29ef4 D_29ef4.
    stepn F_29ef8 D_29ef8. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_29efc D_29efc (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_29f00 D_29f00.
    stepn F_29f04 D_29f04.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_29f08 | reflexivity | exact D_29f08
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_29f0c | reflexivity | exact D_29f0c | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_29f10 | reflexivity | exact D_29f10
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_29f14 D_29f14 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_29f18 D_29f18.
    (* [comment removed for export] *)
    stepb_ft F_29f1c D_29f1c ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_29f20 D_29f20 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_29f44 D_29f44. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_29f48 D_29f48.
    (* [comment removed for export] *)
    stepn F_29d04 D_29d04. sp_renorm.
    stepST F_29d08 D_29d08 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x29f4c) ltac:(sok_stack SOK).
    stepST F_29d0c D_29d0c (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_29d10 D_29d10 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_29d14 D_29d14 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_29d18 D_29d18 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_29d1c D_29d1c.
    stepn F_29d20 D_29d20.
    stepn F_29d24 D_29d24.
    stepn F_29d28 D_29d28.
    stepn F_29d2c D_29d2c.
    (* [comment removed for export] *)
    stepn F_31924 D_31924.
    stepLB0 F_31928 D_31928.
    stepb_tk F_3192c D_3192c ltac:(cond_compute).
    stepretL F_31b1c D_31b1c (0x29d30 : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wN (m : word -> option byte) := wbytes m (Z_to_bv 64 0x64180) [Z_to_bv 8 1].

Section VN.
  Context {fx : FPState}.
Lemma wN : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x64184 -> getr regs 18 = Z_to_bv 64 0x64180 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x64190) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x64184) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x29d30 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0x29f4c : word) (mem_wN (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Malock.
  unfold mem_wN, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_29d30 D_29d30 (Z_to_bv 64 0).
    stepb_tk F_29d34 D_29d34 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_29da4 D_29da4.
    stepST F_29da8 D_29da8 (Z_to_bv 64 0x64180) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_29dac D_29dac. rewrite Hs0.
    (* [comment removed for export] *)
    stepLD8 F_29db0 D_29db0 (Z_to_bv 64 0x29f4c).
    stepLD8 F_29db4 D_29db4 code.
    stepLD8 F_29db8 D_29db8 s1v.
    stepLD8 F_29dbc D_29dbc s2v.
    stepLD8 F_29dc0 D_29dc0 s3v.
    stepn F_29dc4 D_29dc4. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_29dc8 D_29dc8.
    stepLW F_31bac D_31bac 0%Z.
    stepb_ft F_31bb0 D_31bb0 ltac:(cond_compute).
    stepretL F_31bb4 D_31bb4 (0x29f4c : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wO (m : word -> option byte) :=
  wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 0x64188) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x64188) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0x64188) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x64190) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x64180) [Z_to_bv 8 1].

Section VO.
  Context {fx : FPState}.
Lemma wO : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x64184 -> getr regs 18 = Z_to_bv 64 0x64180 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x64190) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x64198)) ->
  rdn RSEGS mem (Z_to_bv 64 0x64188) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
  rdn RSEGS mem (Z_to_bv 64 0x64198) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x641a0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x29e94)) ->
  rdn RSEGS mem (Z_to_bv 64 0x642a0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x152dc)) ->
  rdn RSEGS mem (Z_to_bv 64 0x44044) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x64184) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x643cb) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x29d30 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0x29f4c : word) (mem_wO (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Mslot Mnext Mf0 Ma0 Mcb Malock Mnl.
  unfold mem_wO, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_29d30 D_29d30 (Z_to_bv 64 0x64198).
    stepb_ft F_29d34 D_29d34 ltac:(cond_compute).
    stepLW F_29d38 D_29d38 1%Z.
    stepn F_29d3c D_29d3c.
    (* [comment removed for export] *)
    stepn F_29d54 D_29d54.
    stepST F_29d58 D_29d58 (Z_to_bv 64 0x64188) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_29d5c D_29d5c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_29d60 D_29d60 (Z_to_bv 64 0x64198).
    stepn F_29d64 D_29d64.
    stepn F_29d68 D_29d68.
    stepLD8 F_29d6c D_29d6c (Z_to_bv 64 0x29e94).
    stepLD8 F_29d70 D_29d70 (Z_to_bv 64 0x152dc).
    (* [comment removed for export] *)
    stepn F_29d74 D_29d74. rewrite Hs0.
    stepn F_29d78 D_29d78.
    stepLW F_31bac D_31bac 0%Z.
    stepb_ft F_31bb0 D_31bb0 ltac:(cond_compute).
    stepretL F_31bb4 D_31bb4 (0x29d7c : word).
    (* [comment removed for export] *)
    stepn F_29d7c D_29d7c.
    stepretL F_29d80 D_29d80 (0x29e94 : word).
    stepretL F_29e94 D_29e94 (0x152dc : word).
    (* [comment removed for export] *)
    stepn F_152dc D_152dc.
    stepLBU F_152e0 D_152e0 (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_152e4 D_152e4 ltac:(cond_compute).
    stepretL F_152e8 D_152e8 (0x29d84 : word).
    (* [comment removed for export] *)
    stepn F_29d84 D_29d84.
    stepn F_29d88 D_29d88.
    stepn F_31924 D_31924.
    stepLB0 F_31928 D_31928.
    stepb_tk F_3192c D_3192c ltac:(cond_compute).
    stepretL F_31b1c D_31b1c (0x29d8c : word).
    (* [comment removed for export] *)
    stepLW F_29d8c D_29d8c 0%Z.
    stepn F_29d90 D_29d90.
    stepST F_29d94 D_29d94 (Z_to_bv 64 0x64188) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_29d98 D_29d98 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_29d9c D_29d9c (Z_to_bv 64 0x64198).
    stepn F_29da0 D_29da0.
    stepLD8 F_29d40 D_29d40 (Z_to_bv 64 0).
    stepn F_29d44 D_29d44.
    stepST F_29d48 D_29d48 (Z_to_bv 64 0x64188) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_29d4c D_29d4c (Z_to_bv 64 0x64190) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_29d50 D_29d50 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_29da4 D_29da4.
    stepST F_29da8 D_29da8 (Z_to_bv 64 0x64180) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_29dac D_29dac.
    (* [comment removed for export] *)
    stepLD8 F_29db0 D_29db0 (Z_to_bv 64 0x29f4c).
    stepLD8 F_29db4 D_29db4 code.
    stepLD8 F_29db8 D_29db8 s1v.
    stepLD8 F_29dbc D_29dbc s2v.
    stepLD8 F_29dc0 D_29dc0 s3v.
    stepn F_29dc4 D_29dc4. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_29dc8 D_29dc8.
    stepLW F_31bac D_31bac 0%Z.
    stepb_ft F_31bb0 D_31bb0 ltac:(cond_compute).
    stepretL F_31bb4 D_31bb4 (0x29f4c : word).
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
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x29f50)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x29ecc)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x32d00)))
    (Z_to_bv 64 0x34038) [Z_to_bv 8 1].

Section V2R.
  Context {fx : FPState}.
Lemma w2R : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x32da8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x32d08)) ->
  rdn RSEGS mem (Z_to_bv 64 0x32db0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x32d00)) ->
  rdn RSEGS mem (Z_to_bv 64 0x32d00) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x14e24)) ->
  rdn RSEGS mem (Z_to_bv 64 0x34038) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x32d48) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x29dcc)) ->
  rdn RSEGS mem (Z_to_bv 64 0x32d50) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x33db8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x33db8)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x29f4c : word) mem rom)
                 (mkst regs' (0x2c0b0 : word) (mem_w2R mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x29f54.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mg2 Mdso.
  unfold mem_w2R. eexists. split.
  - (* [comment removed for export] *)
    stepn F_29f4c D_29f4c.
    stepn F_29e9c D_29e9c. rewrite Hsp. sp_renorm.
    stepST F_29ea0 D_29ea0 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x29f50) ltac:(sok_stack SOK).
    stepST F_29ea4 D_29ea4 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_29ea8 D_29ea8 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_29eac D_29eac.
    stepn F_29eb0 D_29eb0.
    stepLD8 F_29eb4 D_29eb4 (Z_to_bv 64 0x32d08).
    stepLD8 F_29eb8 D_29eb8 (Z_to_bv 64 0x32d00).
    (* [comment removed for export] *)
    stepb_ft F_29ebc D_29ebc ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_29ec0 D_29ec0 (Z_to_bv 64 0x14e24).
    stepn F_29ec4 D_29ec4.
    stepretL F_29ec8 D_29ec8 (0x14e24 : word).
    (* [comment removed for export] *)
    stepn F_14e24 D_14e24. sp_renorm.
    stepST F_14e28 D_14e28 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x29ecc) ltac:(sok_stack SOK).
    stepST F_14e2c D_14e2c (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x32d00) ltac:(sok_stack SOK).
    stepn F_14e30 D_14e30.
    stepn F_14e34 D_14e34.
    stepn F_14e38 D_14e38.
    (* [comment removed for export] *)
    stepLBU F_14e3c D_14e3c (Z_to_bv 8 0) ltac:(rewrite ?v_addi_0; rdn_by Mcomp).
    stepn F_14e40 D_14e40.
    stepb_tk F_14e44 D_14e44 ltac:(cond_compute).
    stepn F_14e50 D_14e50.
    stepn F_14e54 D_14e54.
    stepn F_14e58 D_14e58.
    (* [comment removed for export] *)
    stepST F_14e5c D_14e5c (Z_to_bv 64 0x34038) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_14e60 D_14e60.
    stepLD8 F_14e64 D_14e64 (Z_to_bv 64 0x29dcc).
    stepb_ft F_14e68 D_14e68 ltac:(cond_compute).
    stepn F_14e6c D_14e6c.
    stepn F_14e70 D_14e70.
    stepn F_14e74 D_14e74.
    stepLD8 F_14e78 D_14e78 (Z_to_bv 64 0x33db8).
    stepn F_14e7c D_14e7c.
    stepretL F_29dcc D_29dcc (0x14e80 : word).
    stepn F_14e80 D_14e80.
    (* [comment removed for export] *)
    stepn F_14e84 D_14e84.
    stepLD8 F_14e88 D_14e88 (Z_to_bv 64 0).
    stepb_tk F_14e8c D_14e8c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_14ea4 D_14ea4 (Z_to_bv 64 0x29ecc).
    stepLD8 F_14ea8 D_14ea8 (Z_to_bv 64 0x32d00).
    stepn F_14eac D_14eac. sp_renorm.
    stepretL F_14eb0 D_14eb0 (0x29ecc : word).
    (* [comment removed for export] *)
    stepn F_29ecc D_29ecc.
    stepb_ft F_29ed0 D_29ed0 ltac:(cond_compute).
    stepLD8 F_29ed4 D_29ed4 (Z_to_bv 64 0x29f50).
    stepLD8 F_29ed8 D_29ed8 code.
    stepLD8 F_29edc D_29edc s1v.
    stepn F_29ee0 D_29ee0. sp_renorm.
    (* [comment removed for export] *)
    stepn F_29ee4 D_29ee4.
    stepretL F_29e98 D_29e98 (0x29f50 : word).
    stepn F_29f50 D_29f50.
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
    msteps RSEGS (mkst regs (0x29ee8 : word) mem rom) (mkst regs' (0x2c0b0 : word) mem' rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x29f54
    /\ store_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true
    /\ (forall (a : Z) n bs, rdn RSEGS mem (Z_to_bv 64 a) n = Some bs ->
          (0 <= a)%Z -> (a + Z.of_nat n <= 0x65000)%Z ->
          (a + Z.of_nat n <= 0x34038 \/ 0x34039 <= a)%Z ->
          (a + Z.of_nat n <= 0x64180 \/ 0x64198 <= a)%Z ->
          (a + Z.of_nat n <= 0x643a0 \/ 0x643a4 <= a)%Z ->
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
  file_clean mem 0x33ef0 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0x29ee8 : word) mem (seg_rom RSEGS)) model)
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
  assert (FC1 : file_clean mem1 0x33ef0 wp1 rp1).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (FC2 : file_clean mem1 0x33e00 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_clean fx v14_reloc v14_code v14_sites v14_data v14_rw
             regs1 mem1 model sp code wp1 rp1 wp2 rp2 Rsp Rs0 Rra Esplo Esphi SOK1 G1 FC1 FC2 Hh Hlazy).
Qed.
End VP1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stdout_pending_G : forall mem wb wp bufp bufsz rp1 can pending,
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  @StdioDefs.stdout_pending v14_reloc mem wb wp bufp bufsz rp1 can pending.
Proof.
  intros mem wb wp bufp bufsz rp1 can pending [f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14].
  exact (@StdioDefs.Build_stdout_pending v14_reloc mem wb wp bufp bufsz rp1 can pending
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
  realizes RSEGS (mkCfg (mkst regs (0x29ee8 : word) mem (seg_rom RSEGS)) model)
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
  assert (FC2 : file_clean mem1 0x33e00 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (SP1 : stdout_pending mem1 wb wp bufp bufsz rp1 can pending).
  { constructor; zaddr_goal; try assumption.
    1-9: (apply TR; [assumption | cbn; lia ..]).
    - apply TR; [assumption | lia ..].
    - split; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_flush fx v14_reloc v14_code v14_sites v14_data v14_rw
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
  realizes RSEGS (mkCfg (mkst regs (0x29ee8 : word) mem (seg_rom RSEGS)) model)
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
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x29ee8) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending PRE.
  replace (Z_to_bv 64 0x29ee8) with (0x29ee8 : word) by (apply bv_eq; reflexivity).
  exact (ref_exit regs mem model code pending PRE).
Qed.
End VP5.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End V14Exit.
