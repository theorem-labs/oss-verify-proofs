(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.colorfill_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.CliDriver Require Import LibWritevG.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require Import LibAtomic.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Reloc Require Import Reloc RelocKit.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Musl Require Import MuslTac.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Musl Require StdioDefs Exit.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.O8 Require Import O8Kit O8_code_exitpath.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module O8Exit.
Import O8Kit.O8ExitBase.
Import O8Kit.O8StdioDefs.
Import O8Kit.O8Reloc.
Import O8Kit.O8RelocCode.
Import O8Kit.O8RelocSites.
Import O8Kit.O8RelocImg.
Import O8Kit.O8RelocMusl.

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
    (Z_to_bv 64 0x515d0) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x17180)))
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
  rdn RSEGS mem (Z_to_bv 64 0x515d0) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x515fb) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x1711c : word) mem rom)
                 (mkst regs' (0x16f64 : word)
                       (mem_wA mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 64)
    /\ getr regs' 8 = Z_to_bv 64 0x513b4
    /\ getr regs' 18 = Z_to_bv 64 0x513b0.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl.
  unfold mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepn F_1711c D_1711c. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_17120 D_17120 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_17124 D_17124 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_17128 D_17128.
    stepn F_1712c D_1712c. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_17130 D_17130 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_17134 D_17134.
    stepn F_17138 D_17138.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_1713c | reflexivity | exact D_1713c
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_17140 | reflexivity | exact D_17140 | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_17144 | reflexivity | exact D_17144
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_17148 D_17148 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_1714c D_1714c.
    (* [comment removed for export] *)
    stepb_ft F_17150 D_17150 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_17154 D_17154 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_17178 D_17178. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_1717c D_1717c.
    (* [comment removed for export] *)
    stepn F_16f38 D_16f38. sp_renorm.
    stepST F_16f3c D_16f3c (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x17180) ltac:(sok_stack SOK).
    stepST F_16f40 D_16f40 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_16f44 D_16f44 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_16f48 D_16f48 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_16f4c D_16f4c (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_16f50 D_16f50.
    stepn F_16f54 D_16f54.
    stepn F_16f58 D_16f58.
    stepn F_16f5c D_16f5c.
    stepn F_16f60 D_16f60.
    (* [comment removed for export] *)
    stepn F_1eb58 D_1eb58.
    stepLB0 F_1eb5c D_1eb5c.
    stepb_tk F_1eb60 D_1eb60 ltac:(cond_compute).
    stepretL F_1ed50 D_1ed50 (0x16f64 : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wN (m : word -> option byte) := wbytes m (Z_to_bv 64 0x513b0) [Z_to_bv 8 1].

Section VN.
  Context {fx : FPState}.
Lemma wN : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x513b4 -> getr regs 18 = Z_to_bv 64 0x513b0 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x513c0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x513b4) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x16f64 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0x17180 : word) (mem_wN (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Malock.
  unfold mem_wN, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_16f64 D_16f64 (Z_to_bv 64 0).
    stepb_tk F_16f68 D_16f68 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_16fd8 D_16fd8.
    stepST F_16fdc D_16fdc (Z_to_bv 64 0x513b0) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_16fe0 D_16fe0. rewrite Hs0.
    (* [comment removed for export] *)
    stepLD8 F_16fe4 D_16fe4 (Z_to_bv 64 0x17180).
    stepLD8 F_16fe8 D_16fe8 code.
    stepLD8 F_16fec D_16fec s1v.
    stepLD8 F_16ff0 D_16ff0 s2v.
    stepLD8 F_16ff4 D_16ff4 s3v.
    stepn F_16ff8 D_16ff8. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_16ffc D_16ffc.
    stepLW F_1ede0 D_1ede0 0%Z.
    stepb_ft F_1ede4 D_1ede4 ltac:(cond_compute).
    stepretL F_1ede8 D_1ede8 (0x17180 : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wO (m : word -> option byte) :=
  wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 0x513b8) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x513b8) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0x513b8) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x513c0) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x513b0) [Z_to_bv 8 1].

Section VO.
  Context {fx : FPState}.
Lemma wO : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x513b4 -> getr regs 18 = Z_to_bv 64 0x513b0 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x513c0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x513c8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x513b8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
  rdn RSEGS mem (Z_to_bv 64 0x513c8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x513d0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x170c8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x514d0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13c5c)) ->
  rdn RSEGS mem (Z_to_bv 64 0x31274) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x513b4) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x515fb) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x16f64 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0x17180 : word) (mem_wO (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Mslot Mnext Mf0 Ma0 Mcb Malock Mnl.
  unfold mem_wO, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_16f64 D_16f64 (Z_to_bv 64 0x513c8).
    stepb_ft F_16f68 D_16f68 ltac:(cond_compute).
    stepLW F_16f6c D_16f6c 1%Z.
    stepn F_16f70 D_16f70.
    (* [comment removed for export] *)
    stepn F_16f88 D_16f88.
    stepST F_16f8c D_16f8c (Z_to_bv 64 0x513b8) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_16f90 D_16f90 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_16f94 D_16f94 (Z_to_bv 64 0x513c8).
    stepn F_16f98 D_16f98.
    stepn F_16f9c D_16f9c.
    stepLD8 F_16fa0 D_16fa0 (Z_to_bv 64 0x170c8).
    stepLD8 F_16fa4 D_16fa4 (Z_to_bv 64 0x13c5c).
    (* [comment removed for export] *)
    stepn F_16fa8 D_16fa8. rewrite Hs0.
    stepn F_16fac D_16fac.
    stepLW F_1ede0 D_1ede0 0%Z.
    stepb_ft F_1ede4 D_1ede4 ltac:(cond_compute).
    stepretL F_1ede8 D_1ede8 (0x16fb0 : word).
    (* [comment removed for export] *)
    stepn F_16fb0 D_16fb0.
    stepretL F_16fb4 D_16fb4 (0x170c8 : word).
    stepretL F_170c8 D_170c8 (0x13c5c : word).
    (* [comment removed for export] *)
    stepn F_13c5c D_13c5c.
    stepLBU F_13c60 D_13c60 (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_13c64 D_13c64 ltac:(cond_compute).
    stepretL F_13c68 D_13c68 (0x16fb8 : word).
    (* [comment removed for export] *)
    stepn F_16fb8 D_16fb8.
    stepn F_16fbc D_16fbc.
    stepn F_1eb58 D_1eb58.
    stepLB0 F_1eb5c D_1eb5c.
    stepb_tk F_1eb60 D_1eb60 ltac:(cond_compute).
    stepretL F_1ed50 D_1ed50 (0x16fc0 : word).
    (* [comment removed for export] *)
    stepLW F_16fc0 D_16fc0 0%Z.
    stepn F_16fc4 D_16fc4.
    stepST F_16fc8 D_16fc8 (Z_to_bv 64 0x513b8) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_16fcc D_16fcc ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_16fd0 D_16fd0 (Z_to_bv 64 0x513c8).
    stepn F_16fd4 D_16fd4.
    stepLD8 F_16f74 D_16f74 (Z_to_bv 64 0).
    stepn F_16f78 D_16f78.
    stepST F_16f7c D_16f7c (Z_to_bv 64 0x513b8) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_16f80 D_16f80 (Z_to_bv 64 0x513c0) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_16f84 D_16f84 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_16fd8 D_16fd8.
    stepST F_16fdc D_16fdc (Z_to_bv 64 0x513b0) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_16fe0 D_16fe0.
    (* [comment removed for export] *)
    stepLD8 F_16fe4 D_16fe4 (Z_to_bv 64 0x17180).
    stepLD8 F_16fe8 D_16fe8 code.
    stepLD8 F_16fec D_16fec s1v.
    stepLD8 F_16ff0 D_16ff0 s2v.
    stepLD8 F_16ff4 D_16ff4 s3v.
    stepn F_16ff8 D_16ff8. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_16ffc D_16ffc.
    stepLW F_1ede0 D_1ede0 0%Z.
    stepb_ft F_1ede4 D_1ede4 ltac:(cond_compute).
    stepretL F_1ede8 D_1ede8 (0x17180 : word).
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
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x17184)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x17100)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x1ff30)))
    (Z_to_bv 64 0x21268) [Z_to_bv 8 1].

Section V2R.
  Context {fx : FPState}.
Lemma w2R : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x1ffd8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1ff38)) ->
  rdn RSEGS mem (Z_to_bv 64 0x1ffe0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1ff30)) ->
  rdn RSEGS mem (Z_to_bv 64 0x1ff30) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x137a4)) ->
  rdn RSEGS mem (Z_to_bv 64 0x21268) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x1ff78) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x17000)) ->
  rdn RSEGS mem (Z_to_bv 64 0x1ff80) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x20fe8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x20fe8)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x17180 : word) mem rom)
                 (mkst regs' (0x192e4 : word) (mem_w2R mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x17188.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mg2 Mdso.
  unfold mem_w2R. eexists. split.
  - (* [comment removed for export] *)
    stepn F_17180 D_17180.
    stepn F_170d0 D_170d0. rewrite Hsp. sp_renorm.
    stepST F_170d4 D_170d4 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x17184) ltac:(sok_stack SOK).
    stepST F_170d8 D_170d8 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_170dc D_170dc (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_170e0 D_170e0.
    stepn F_170e4 D_170e4.
    stepLD8 F_170e8 D_170e8 (Z_to_bv 64 0x1ff38).
    stepLD8 F_170ec D_170ec (Z_to_bv 64 0x1ff30).
    (* [comment removed for export] *)
    stepb_ft F_170f0 D_170f0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_170f4 D_170f4 (Z_to_bv 64 0x137a4).
    stepn F_170f8 D_170f8.
    stepretL F_170fc D_170fc (0x137a4 : word).
    (* [comment removed for export] *)
    stepn F_137a4 D_137a4. sp_renorm.
    stepST F_137a8 D_137a8 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x17100) ltac:(sok_stack SOK).
    stepST F_137ac D_137ac (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x1ff30) ltac:(sok_stack SOK).
    stepn F_137b0 D_137b0.
    stepn F_137b4 D_137b4.
    stepn F_137b8 D_137b8.
    (* [comment removed for export] *)
    stepLBU F_137bc D_137bc (Z_to_bv 8 0) ltac:(rewrite ?v_addi_0; rdn_by Mcomp).
    stepn F_137c0 D_137c0.
    stepb_tk F_137c4 D_137c4 ltac:(cond_compute).
    stepn F_137d0 D_137d0.
    stepn F_137d4 D_137d4.
    stepn F_137d8 D_137d8.
    (* [comment removed for export] *)
    stepST F_137dc D_137dc (Z_to_bv 64 0x21268) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_137e0 D_137e0.
    stepLD8 F_137e4 D_137e4 (Z_to_bv 64 0x17000).
    stepb_ft F_137e8 D_137e8 ltac:(cond_compute).
    stepn F_137ec D_137ec.
    stepn F_137f0 D_137f0.
    stepn F_137f4 D_137f4.
    stepLD8 F_137f8 D_137f8 (Z_to_bv 64 0x20fe8).
    stepn F_137fc D_137fc.
    stepretL F_17000 D_17000 (0x13800 : word).
    stepn F_13800 D_13800.
    (* [comment removed for export] *)
    stepn F_13804 D_13804.
    stepLD8 F_13808 D_13808 (Z_to_bv 64 0).
    stepb_tk F_1380c D_1380c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_13824 D_13824 (Z_to_bv 64 0x17100).
    stepLD8 F_13828 D_13828 (Z_to_bv 64 0x1ff30).
    stepn F_1382c D_1382c. sp_renorm.
    stepretL F_13830 D_13830 (0x17100 : word).
    (* [comment removed for export] *)
    stepn F_17100 D_17100.
    stepb_ft F_17104 D_17104 ltac:(cond_compute).
    stepLD8 F_17108 D_17108 (Z_to_bv 64 0x17184).
    stepLD8 F_1710c D_1710c code.
    stepLD8 F_17110 D_17110 s1v.
    stepn F_17114 D_17114. sp_renorm.
    (* [comment removed for export] *)
    stepn F_17118 D_17118.
    stepretL F_170cc D_170cc (0x17184 : word).
    stepn F_17184 D_17184.
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
    msteps RSEGS (mkst regs (0x1711c : word) mem rom) (mkst regs' (0x192e4 : word) mem' rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x17188
    /\ store_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true
    /\ (forall (a : Z) n bs, rdn RSEGS mem (Z_to_bv 64 a) n = Some bs ->
          (0 <= a)%Z -> (a + Z.of_nat n <= 0x52000)%Z ->
          (a + Z.of_nat n <= 0x21268 \/ 0x21269 <= a)%Z ->
          (a + Z.of_nat n <= 0x513b0 \/ 0x513c8 <= a)%Z ->
          (a + Z.of_nat n <= 0x515d0 \/ 0x515d4 <= a)%Z ->
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
  file_clean mem 0x21120 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0x1711c : word) mem (seg_rom RSEGS)) model)
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
  assert (FC1 : file_clean mem1 0x21120 wp1 rp1).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (FC2 : file_clean mem1 0x21030 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_clean fx o8_reloc o8_code o8_sites o8_data o8_rw
             regs1 mem1 model sp code wp1 rp1 wp2 rp2 Rsp Rs0 Rra Esplo Esphi SOK1 G1 FC1 FC2 Hh Hlazy).
Qed.
End VP1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stdout_pending_G : forall mem wb wp bufp bufsz rp1 can pending,
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  @StdioDefs.stdout_pending o8_reloc mem wb wp bufp bufsz rp1 can pending.
Proof.
  intros mem wb wp bufp bufsz rp1 can pending [f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14].
  exact (@StdioDefs.Build_stdout_pending o8_reloc mem wb wp bufp bufsz rp1 can pending
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
  realizes RSEGS (mkCfg (mkst regs (0x1711c : word) mem (seg_rom RSEGS)) model)
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
  assert (FC2 : file_clean mem1 0x21030 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (SP1 : stdout_pending mem1 wb wp bufp bufsz rp1 can pending).
  { constructor; zaddr_goal; try assumption.
    1-9: (apply TR; [assumption | cbn; lia ..]).
    - apply TR; [assumption | lia ..].
    - split; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_flush fx o8_reloc o8_code o8_sites o8_data o8_rw
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
  realizes RSEGS (mkCfg (mkst regs (0x1711c : word) mem (seg_rom RSEGS)) model)
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
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x1711c) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending PRE.
  replace (Z_to_bv 64 0x1711c) with (0x1711c : word) by (apply bv_eq; reflexivity).
  exact (ref_exit regs mem model code pending PRE).
Qed.
End VP5.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End O8Exit.
