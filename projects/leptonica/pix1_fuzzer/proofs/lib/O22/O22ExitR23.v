(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix1_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.CliDriver Require Import LibWritevG.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica Require Import LibAtomic.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Reloc Require Import Reloc RelocKit.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Musl Require Import MuslTac.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Musl Require StdioDefs Exit.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.O22 Require Import O22Kit O22_code_exitpath.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module O22Exit.
Import O22Kit.O22ExitBase.
Import O22Kit.O22StdioDefs.
Import O22Kit.O22Reloc.
Import O22Kit.O22RelocCode.
Import O22Kit.O22RelocSites.
Import O22Kit.O22RelocImg.
Import O22Kit.O22RelocMusl.

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
    (Z_to_bv 64 0x4fe00) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x159ac)))
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
  rdn RSEGS mem (Z_to_bv 64 0x4fe00) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x4fe2b) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x15948 : word) mem rom)
                 (mkst regs' (0x15790 : word)
                       (mem_wA mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 64)
    /\ getr regs' 8 = Z_to_bv 64 0x4fbe4
    /\ getr regs' 18 = Z_to_bv 64 0x4fbe0.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl.
  unfold mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepn F_15948 D_15948. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_1594c D_1594c (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_15950 D_15950 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_15954 D_15954.
    stepn F_15958 D_15958. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_1595c D_1595c (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_15960 D_15960.
    stepn F_15964 D_15964.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_15968 | reflexivity | exact D_15968
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_1596c | reflexivity | exact D_1596c | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_15970 | reflexivity | exact D_15970
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_15974 D_15974 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_15978 D_15978.
    (* [comment removed for export] *)
    stepb_ft F_1597c D_1597c ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_15980 D_15980 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_159a4 D_159a4. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_159a8 D_159a8.
    (* [comment removed for export] *)
    stepn F_15764 D_15764. sp_renorm.
    stepST F_15768 D_15768 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x159ac) ltac:(sok_stack SOK).
    stepST F_1576c D_1576c (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_15770 D_15770 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_15774 D_15774 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_15778 D_15778 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_1577c D_1577c.
    stepn F_15780 D_15780.
    stepn F_15784 D_15784.
    stepn F_15788 D_15788.
    stepn F_1578c D_1578c.
    (* [comment removed for export] *)
    stepn F_1d384 D_1d384.
    stepLB0 F_1d388 D_1d388.
    stepb_tk F_1d38c D_1d38c ltac:(cond_compute).
    stepretL F_1d57c D_1d57c (0x15790 : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wN (m : word -> option byte) := wbytes m (Z_to_bv 64 0x4fbe0) [Z_to_bv 8 1].

Section VN.
  Context {fx : FPState}.
Lemma wN : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x4fbe4 -> getr regs 18 = Z_to_bv 64 0x4fbe0 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x4fbf0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x4fbe4) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x15790 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0x159ac : word) (mem_wN (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Malock.
  unfold mem_wN, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_15790 D_15790 (Z_to_bv 64 0).
    stepb_tk F_15794 D_15794 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_15804 D_15804.
    stepST F_15808 D_15808 (Z_to_bv 64 0x4fbe0) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_1580c D_1580c. rewrite Hs0.
    (* [comment removed for export] *)
    stepLD8 F_15810 D_15810 (Z_to_bv 64 0x159ac).
    stepLD8 F_15814 D_15814 code.
    stepLD8 F_15818 D_15818 s1v.
    stepLD8 F_1581c D_1581c s2v.
    stepLD8 F_15820 D_15820 s3v.
    stepn F_15824 D_15824. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_15828 D_15828.
    stepLW F_1d60c D_1d60c 0%Z.
    stepb_ft F_1d610 D_1d610 ltac:(cond_compute).
    stepretL F_1d614 D_1d614 (0x159ac : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wO (m : word -> option byte) :=
  wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 0x4fbe8) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x4fbe8) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0x4fbe8) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x4fbf0) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x4fbe0) [Z_to_bv 8 1].

Section VO.
  Context {fx : FPState}.
Lemma wO : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x4fbe4 -> getr regs 18 = Z_to_bv 64 0x4fbe0 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x4fbf0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x4fbf8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x4fbe8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
  rdn RSEGS mem (Z_to_bv 64 0x4fbf8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x4fc00) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x158f4)) ->
  rdn RSEGS mem (Z_to_bv 64 0x4fd00) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1360c)) ->
  rdn RSEGS mem (Z_to_bv 64 0x2faa4) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x4fbe4) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x4fe2b) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x15790 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0x159ac : word) (mem_wO (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Mslot Mnext Mf0 Ma0 Mcb Malock Mnl.
  unfold mem_wO, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_15790 D_15790 (Z_to_bv 64 0x4fbf8).
    stepb_ft F_15794 D_15794 ltac:(cond_compute).
    stepLW F_15798 D_15798 1%Z.
    stepn F_1579c D_1579c.
    (* [comment removed for export] *)
    stepn F_157b4 D_157b4.
    stepST F_157b8 D_157b8 (Z_to_bv 64 0x4fbe8) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_157bc D_157bc ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_157c0 D_157c0 (Z_to_bv 64 0x4fbf8).
    stepn F_157c4 D_157c4.
    stepn F_157c8 D_157c8.
    stepLD8 F_157cc D_157cc (Z_to_bv 64 0x158f4).
    stepLD8 F_157d0 D_157d0 (Z_to_bv 64 0x1360c).
    (* [comment removed for export] *)
    stepn F_157d4 D_157d4. rewrite Hs0.
    stepn F_157d8 D_157d8.
    stepLW F_1d60c D_1d60c 0%Z.
    stepb_ft F_1d610 D_1d610 ltac:(cond_compute).
    stepretL F_1d614 D_1d614 (0x157dc : word).
    (* [comment removed for export] *)
    stepn F_157dc D_157dc.
    stepretL F_157e0 D_157e0 (0x158f4 : word).
    stepretL F_158f4 D_158f4 (0x1360c : word).
    (* [comment removed for export] *)
    stepn F_1360c D_1360c.
    stepLBU F_13610 D_13610 (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_13614 D_13614 ltac:(cond_compute).
    stepretL F_13618 D_13618 (0x157e4 : word).
    (* [comment removed for export] *)
    stepn F_157e4 D_157e4.
    stepn F_157e8 D_157e8.
    stepn F_1d384 D_1d384.
    stepLB0 F_1d388 D_1d388.
    stepb_tk F_1d38c D_1d38c ltac:(cond_compute).
    stepretL F_1d57c D_1d57c (0x157ec : word).
    (* [comment removed for export] *)
    stepLW F_157ec D_157ec 0%Z.
    stepn F_157f0 D_157f0.
    stepST F_157f4 D_157f4 (Z_to_bv 64 0x4fbe8) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_157f8 D_157f8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_157fc D_157fc (Z_to_bv 64 0x4fbf8).
    stepn F_15800 D_15800.
    stepLD8 F_157a0 D_157a0 (Z_to_bv 64 0).
    stepn F_157a4 D_157a4.
    stepST F_157a8 D_157a8 (Z_to_bv 64 0x4fbe8) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_157ac D_157ac (Z_to_bv 64 0x4fbf0) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_157b0 D_157b0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_15804 D_15804.
    stepST F_15808 D_15808 (Z_to_bv 64 0x4fbe0) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_1580c D_1580c.
    (* [comment removed for export] *)
    stepLD8 F_15810 D_15810 (Z_to_bv 64 0x159ac).
    stepLD8 F_15814 D_15814 code.
    stepLD8 F_15818 D_15818 s1v.
    stepLD8 F_1581c D_1581c s2v.
    stepLD8 F_15820 D_15820 s3v.
    stepn F_15824 D_15824. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_15828 D_15828.
    stepLW F_1d60c D_1d60c 0%Z.
    stepb_ft F_1d610 D_1d610 ltac:(cond_compute).
    stepretL F_1d614 D_1d614 (0x159ac : word).
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
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x159b0)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x1592c)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x1e760)))
    (Z_to_bv 64 0x1fa98) [Z_to_bv 8 1].

Section V2R.
  Context {fx : FPState}.
Lemma w2R : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x1e808) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1e768)) ->
  rdn RSEGS mem (Z_to_bv 64 0x1e810) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1e760)) ->
  rdn RSEGS mem (Z_to_bv 64 0x1e760) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13154)) ->
  rdn RSEGS mem (Z_to_bv 64 0x1fa98) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x1e7a8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1582c)) ->
  rdn RSEGS mem (Z_to_bv 64 0x1e7b0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x1f818) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1f818)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x159ac : word) mem rom)
                 (mkst regs' (0x17b10 : word) (mem_w2R mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x159b4.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mg2 Mdso.
  unfold mem_w2R. eexists. split.
  - (* [comment removed for export] *)
    stepn F_159ac D_159ac.
    stepn F_158fc D_158fc. rewrite Hsp. sp_renorm.
    stepST F_15900 D_15900 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x159b0) ltac:(sok_stack SOK).
    stepST F_15904 D_15904 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_15908 D_15908 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_1590c D_1590c.
    stepn F_15910 D_15910.
    stepLD8 F_15914 D_15914 (Z_to_bv 64 0x1e768).
    stepLD8 F_15918 D_15918 (Z_to_bv 64 0x1e760).
    (* [comment removed for export] *)
    stepb_ft F_1591c D_1591c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_15920 D_15920 (Z_to_bv 64 0x13154).
    stepn F_15924 D_15924.
    stepretL F_15928 D_15928 (0x13154 : word).
    (* [comment removed for export] *)
    stepn F_13154 D_13154. sp_renorm.
    stepST F_13158 D_13158 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x1592c) ltac:(sok_stack SOK).
    stepST F_1315c D_1315c (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x1e760) ltac:(sok_stack SOK).
    stepn F_13160 D_13160.
    stepn F_13164 D_13164.
    stepn F_13168 D_13168.
    (* [comment removed for export] *)
    stepLBU F_1316c D_1316c (Z_to_bv 8 0) ltac:(rewrite ?v_addi_0; rdn_by Mcomp).
    stepn F_13170 D_13170.
    stepb_tk F_13174 D_13174 ltac:(cond_compute).
    stepn F_13180 D_13180.
    stepn F_13184 D_13184.
    stepn F_13188 D_13188.
    (* [comment removed for export] *)
    stepST F_1318c D_1318c (Z_to_bv 64 0x1fa98) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_13190 D_13190.
    stepLD8 F_13194 D_13194 (Z_to_bv 64 0x1582c).
    stepb_ft F_13198 D_13198 ltac:(cond_compute).
    stepn F_1319c D_1319c.
    stepn F_131a0 D_131a0.
    stepn F_131a4 D_131a4.
    stepLD8 F_131a8 D_131a8 (Z_to_bv 64 0x1f818).
    stepn F_131ac D_131ac.
    stepretL F_1582c D_1582c (0x131b0 : word).
    stepn F_131b0 D_131b0.
    (* [comment removed for export] *)
    stepn F_131b4 D_131b4.
    stepLD8 F_131b8 D_131b8 (Z_to_bv 64 0).
    stepb_tk F_131bc D_131bc ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_131d4 D_131d4 (Z_to_bv 64 0x1592c).
    stepLD8 F_131d8 D_131d8 (Z_to_bv 64 0x1e760).
    stepn F_131dc D_131dc. sp_renorm.
    stepretL F_131e0 D_131e0 (0x1592c : word).
    (* [comment removed for export] *)
    stepn F_1592c D_1592c.
    stepb_ft F_15930 D_15930 ltac:(cond_compute).
    stepLD8 F_15934 D_15934 (Z_to_bv 64 0x159b0).
    stepLD8 F_15938 D_15938 code.
    stepLD8 F_1593c D_1593c s1v.
    stepn F_15940 D_15940. sp_renorm.
    (* [comment removed for export] *)
    stepn F_15944 D_15944.
    stepretL F_158f8 D_158f8 (0x159b0 : word).
    stepn F_159b0 D_159b0.
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
    msteps RSEGS (mkst regs (0x15948 : word) mem rom) (mkst regs' (0x17b10 : word) mem' rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x159b4
    /\ store_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true
    /\ (forall (a : Z) n bs, rdn RSEGS mem (Z_to_bv 64 a) n = Some bs ->
          (0 <= a)%Z -> (a + Z.of_nat n <= 0x51000)%Z ->
          (a + Z.of_nat n <= 0x1fa98 \/ 0x1fa99 <= a)%Z ->
          (a + Z.of_nat n <= 0x4fbe0 \/ 0x4fbf8 <= a)%Z ->
          (a + Z.of_nat n <= 0x4fe00 \/ 0x4fe04 <= a)%Z ->
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
  file_clean mem 0x1f950 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0x15948 : word) mem (seg_rom RSEGS)) model)
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
  assert (FC1 : file_clean mem1 0x1f950 wp1 rp1).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (FC2 : file_clean mem1 0x1f860 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_clean fx o22_reloc o22_code o22_sites o22_data o22_rw
             regs1 mem1 model sp code wp1 rp1 wp2 rp2 Rsp Rs0 Rra Esplo Esphi SOK1 G1 FC1 FC2 Hh Hlazy).
Qed.
End VP1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stdout_pending_G : forall mem wb wp bufp bufsz rp1 can pending,
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  @StdioDefs.stdout_pending o22_reloc mem wb wp bufp bufsz rp1 can pending.
Proof.
  intros mem wb wp bufp bufsz rp1 can pending [f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14].
  exact (@StdioDefs.Build_stdout_pending o22_reloc mem wb wp bufp bufsz rp1 can pending
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
  realizes RSEGS (mkCfg (mkst regs (0x15948 : word) mem (seg_rom RSEGS)) model)
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
  assert (FC2 : file_clean mem1 0x1f860 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (SP1 : stdout_pending mem1 wb wp bufp bufsz rp1 can pending).
  { constructor; zaddr_goal; try assumption.
    1-9: (apply TR; [assumption | cbn; lia ..]).
    - apply TR; [assumption | lia ..].
    - split; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_flush fx o22_reloc o22_code o22_sites o22_data o22_rw
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
  realizes RSEGS (mkCfg (mkst regs (0x15948 : word) mem (seg_rom RSEGS)) model)
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
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x15948) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending PRE.
  replace (Z_to_bv 64 0x15948) with (0x15948 : word) by (apply bv_eq; reflexivity).
  exact (ref_exit regs mem model code pending PRE).
Qed.
End VP5.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End O22Exit.
