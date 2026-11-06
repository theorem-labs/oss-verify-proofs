(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.kernel_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver Require Import LibWritevG.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import LibAtomic.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc Require Import Reloc RelocKit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl Require Import MuslTac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl Require StdioDefs Exit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require Import O17Kit O17_code_exitpath.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module O17Exit.
Import O17Kit.O17ExitBase.
Import O17Kit.O17StdioDefs.
Import O17Kit.O17Reloc.
Import O17Kit.O17RelocCode.
Import O17Kit.O17RelocSites.
Import O17Kit.O17RelocImg.
Import O17Kit.O17RelocMusl.

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
    (Z_to_bv 64 0x50780) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x16330)))
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
  rdn RSEGS mem (Z_to_bv 64 0x50780) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x507ab) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x162cc : word) mem rom)
                 (mkst regs' (0x16114 : word)
                       (mem_wA mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 64)
    /\ getr regs' 8 = Z_to_bv 64 0x50564
    /\ getr regs' 18 = Z_to_bv 64 0x50560.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl.
  unfold mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepn F_162cc D_162cc. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_162d0 D_162d0 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_162d4 D_162d4 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_162d8 D_162d8.
    stepn F_162dc D_162dc. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_162e0 D_162e0 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_162e4 D_162e4.
    stepn F_162e8 D_162e8.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_162ec | reflexivity | exact D_162ec
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_162f0 | reflexivity | exact D_162f0 | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_162f4 | reflexivity | exact D_162f4
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_162f8 D_162f8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_162fc D_162fc.
    (* [comment removed for export] *)
    stepb_ft F_16300 D_16300 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_16304 D_16304 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_16328 D_16328. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_1632c D_1632c.
    (* [comment removed for export] *)
    stepn F_160e8 D_160e8. sp_renorm.
    stepST F_160ec D_160ec (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x16330) ltac:(sok_stack SOK).
    stepST F_160f0 D_160f0 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_160f4 D_160f4 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_160f8 D_160f8 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_160fc D_160fc (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_16100 D_16100.
    stepn F_16104 D_16104.
    stepn F_16108 D_16108.
    stepn F_1610c D_1610c.
    stepn F_16110 D_16110.
    (* [comment removed for export] *)
    stepn F_1dd08 D_1dd08.
    stepLB0 F_1dd0c D_1dd0c.
    stepb_tk F_1dd10 D_1dd10 ltac:(cond_compute).
    stepretL F_1df00 D_1df00 (0x16114 : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wN (m : word -> option byte) := wbytes m (Z_to_bv 64 0x50560) [Z_to_bv 8 1].

Section VN.
  Context {fx : FPState}.
Lemma wN : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x50564 -> getr regs 18 = Z_to_bv 64 0x50560 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x50570) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x50564) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x16114 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0x16330 : word) (mem_wN (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Malock.
  unfold mem_wN, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_16114 D_16114 (Z_to_bv 64 0).
    stepb_tk F_16118 D_16118 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_16188 D_16188.
    stepST F_1618c D_1618c (Z_to_bv 64 0x50560) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_16190 D_16190. rewrite Hs0.
    (* [comment removed for export] *)
    stepLD8 F_16194 D_16194 (Z_to_bv 64 0x16330).
    stepLD8 F_16198 D_16198 code.
    stepLD8 F_1619c D_1619c s1v.
    stepLD8 F_161a0 D_161a0 s2v.
    stepLD8 F_161a4 D_161a4 s3v.
    stepn F_161a8 D_161a8. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_161ac D_161ac.
    stepLW F_1df90 D_1df90 0%Z.
    stepb_ft F_1df94 D_1df94 ltac:(cond_compute).
    stepretL F_1df98 D_1df98 (0x16330 : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wO (m : word -> option byte) :=
  wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 0x50568) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x50568) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0x50568) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x50570) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x50560) [Z_to_bv 8 1].

Section VO.
  Context {fx : FPState}.
Lemma wO : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x50564 -> getr regs 18 = Z_to_bv 64 0x50560 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x50570) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x50578)) ->
  rdn RSEGS mem (Z_to_bv 64 0x50568) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
  rdn RSEGS mem (Z_to_bv 64 0x50578) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x50580) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x16278)) ->
  rdn RSEGS mem (Z_to_bv 64 0x50680) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x138dc)) ->
  rdn RSEGS mem (Z_to_bv 64 0x30424) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x50564) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x507ab) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x16114 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0x16330 : word) (mem_wO (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Mslot Mnext Mf0 Ma0 Mcb Malock Mnl.
  unfold mem_wO, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_16114 D_16114 (Z_to_bv 64 0x50578).
    stepb_ft F_16118 D_16118 ltac:(cond_compute).
    stepLW F_1611c D_1611c 1%Z.
    stepn F_16120 D_16120.
    (* [comment removed for export] *)
    stepn F_16138 D_16138.
    stepST F_1613c D_1613c (Z_to_bv 64 0x50568) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_16140 D_16140 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_16144 D_16144 (Z_to_bv 64 0x50578).
    stepn F_16148 D_16148.
    stepn F_1614c D_1614c.
    stepLD8 F_16150 D_16150 (Z_to_bv 64 0x16278).
    stepLD8 F_16154 D_16154 (Z_to_bv 64 0x138dc).
    (* [comment removed for export] *)
    stepn F_16158 D_16158. rewrite Hs0.
    stepn F_1615c D_1615c.
    stepLW F_1df90 D_1df90 0%Z.
    stepb_ft F_1df94 D_1df94 ltac:(cond_compute).
    stepretL F_1df98 D_1df98 (0x16160 : word).
    (* [comment removed for export] *)
    stepn F_16160 D_16160.
    stepretL F_16164 D_16164 (0x16278 : word).
    stepretL F_16278 D_16278 (0x138dc : word).
    (* [comment removed for export] *)
    stepn F_138dc D_138dc.
    stepLBU F_138e0 D_138e0 (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_138e4 D_138e4 ltac:(cond_compute).
    stepretL F_138e8 D_138e8 (0x16168 : word).
    (* [comment removed for export] *)
    stepn F_16168 D_16168.
    stepn F_1616c D_1616c.
    stepn F_1dd08 D_1dd08.
    stepLB0 F_1dd0c D_1dd0c.
    stepb_tk F_1dd10 D_1dd10 ltac:(cond_compute).
    stepretL F_1df00 D_1df00 (0x16170 : word).
    (* [comment removed for export] *)
    stepLW F_16170 D_16170 0%Z.
    stepn F_16174 D_16174.
    stepST F_16178 D_16178 (Z_to_bv 64 0x50568) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_1617c D_1617c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_16180 D_16180 (Z_to_bv 64 0x50578).
    stepn F_16184 D_16184.
    stepLD8 F_16124 D_16124 (Z_to_bv 64 0).
    stepn F_16128 D_16128.
    stepST F_1612c D_1612c (Z_to_bv 64 0x50568) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_16130 D_16130 (Z_to_bv 64 0x50570) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_16134 D_16134 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_16188 D_16188.
    stepST F_1618c D_1618c (Z_to_bv 64 0x50560) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_16190 D_16190.
    (* [comment removed for export] *)
    stepLD8 F_16194 D_16194 (Z_to_bv 64 0x16330).
    stepLD8 F_16198 D_16198 code.
    stepLD8 F_1619c D_1619c s1v.
    stepLD8 F_161a0 D_161a0 s2v.
    stepLD8 F_161a4 D_161a4 s3v.
    stepn F_161a8 D_161a8. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_161ac D_161ac.
    stepLW F_1df90 D_1df90 0%Z.
    stepb_ft F_1df94 D_1df94 ltac:(cond_compute).
    stepretL F_1df98 D_1df98 (0x16330 : word).
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
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x16334)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x162b0)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x1f0e0)))
    (Z_to_bv 64 0x20418) [Z_to_bv 8 1].

Section V2R.
  Context {fx : FPState}.
Lemma w2R : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x1f188) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1f0e8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x1f190) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1f0e0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x1f0e0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13424)) ->
  rdn RSEGS mem (Z_to_bv 64 0x20418) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x1f128) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x161b0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x1f130) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x20198) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x20198)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x16330 : word) mem rom)
                 (mkst regs' (0x18494 : word) (mem_w2R mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x16338.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mg2 Mdso.
  unfold mem_w2R. eexists. split.
  - (* [comment removed for export] *)
    stepn F_16330 D_16330.
    stepn F_16280 D_16280. rewrite Hsp. sp_renorm.
    stepST F_16284 D_16284 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x16334) ltac:(sok_stack SOK).
    stepST F_16288 D_16288 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_1628c D_1628c (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_16290 D_16290.
    stepn F_16294 D_16294.
    stepLD8 F_16298 D_16298 (Z_to_bv 64 0x1f0e8).
    stepLD8 F_1629c D_1629c (Z_to_bv 64 0x1f0e0).
    (* [comment removed for export] *)
    stepb_ft F_162a0 D_162a0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_162a4 D_162a4 (Z_to_bv 64 0x13424).
    stepn F_162a8 D_162a8.
    stepretL F_162ac D_162ac (0x13424 : word).
    (* [comment removed for export] *)
    stepn F_13424 D_13424. sp_renorm.
    stepST F_13428 D_13428 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x162b0) ltac:(sok_stack SOK).
    stepST F_1342c D_1342c (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x1f0e0) ltac:(sok_stack SOK).
    stepn F_13430 D_13430.
    stepn F_13434 D_13434.
    stepn F_13438 D_13438.
    (* [comment removed for export] *)
    stepLBU F_1343c D_1343c (Z_to_bv 8 0) ltac:(rewrite ?v_addi_0; rdn_by Mcomp).
    stepn F_13440 D_13440.
    stepb_tk F_13444 D_13444 ltac:(cond_compute).
    stepn F_13450 D_13450.
    stepn F_13454 D_13454.
    stepn F_13458 D_13458.
    (* [comment removed for export] *)
    stepST F_1345c D_1345c (Z_to_bv 64 0x20418) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_13460 D_13460.
    stepLD8 F_13464 D_13464 (Z_to_bv 64 0x161b0).
    stepb_ft F_13468 D_13468 ltac:(cond_compute).
    stepn F_1346c D_1346c.
    stepn F_13470 D_13470.
    stepn F_13474 D_13474.
    stepLD8 F_13478 D_13478 (Z_to_bv 64 0x20198).
    stepn F_1347c D_1347c.
    stepretL F_161b0 D_161b0 (0x13480 : word).
    stepn F_13480 D_13480.
    (* [comment removed for export] *)
    stepn F_13484 D_13484.
    stepLD8 F_13488 D_13488 (Z_to_bv 64 0).
    stepb_tk F_1348c D_1348c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_134a4 D_134a4 (Z_to_bv 64 0x162b0).
    stepLD8 F_134a8 D_134a8 (Z_to_bv 64 0x1f0e0).
    stepn F_134ac D_134ac. sp_renorm.
    stepretL F_134b0 D_134b0 (0x162b0 : word).
    (* [comment removed for export] *)
    stepn F_162b0 D_162b0.
    stepb_ft F_162b4 D_162b4 ltac:(cond_compute).
    stepLD8 F_162b8 D_162b8 (Z_to_bv 64 0x16334).
    stepLD8 F_162bc D_162bc code.
    stepLD8 F_162c0 D_162c0 s1v.
    stepn F_162c4 D_162c4. sp_renorm.
    (* [comment removed for export] *)
    stepn F_162c8 D_162c8.
    stepretL F_1627c D_1627c (0x16334 : word).
    stepn F_16334 D_16334.
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
    msteps RSEGS (mkst regs (0x162cc : word) mem rom) (mkst regs' (0x18494 : word) mem' rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x16338
    /\ store_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true
    /\ (forall (a : Z) n bs, rdn RSEGS mem (Z_to_bv 64 a) n = Some bs ->
          (0 <= a)%Z -> (a + Z.of_nat n <= 0x51000)%Z ->
          (a + Z.of_nat n <= 0x20418 \/ 0x20419 <= a)%Z ->
          (a + Z.of_nat n <= 0x50560 \/ 0x50578 <= a)%Z ->
          (a + Z.of_nat n <= 0x50780 \/ 0x50784 <= a)%Z ->
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
  file_clean mem 0x202d0 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0x162cc : word) mem (seg_rom RSEGS)) model)
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
  assert (FC1 : file_clean mem1 0x202d0 wp1 rp1).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (FC2 : file_clean mem1 0x201e0 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_clean fx o17_reloc o17_code o17_sites o17_data o17_rw
             regs1 mem1 model sp code wp1 rp1 wp2 rp2 Rsp Rs0 Rra Esplo Esphi SOK1 G1 FC1 FC2 Hh Hlazy).
Qed.
End VP1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stdout_pending_G : forall mem wb wp bufp bufsz rp1 can pending,
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  @StdioDefs.stdout_pending o17_reloc mem wb wp bufp bufsz rp1 can pending.
Proof.
  intros mem wb wp bufp bufsz rp1 can pending [f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14].
  exact (@StdioDefs.Build_stdout_pending o17_reloc mem wb wp bufp bufsz rp1 can pending
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
  realizes RSEGS (mkCfg (mkst regs (0x162cc : word) mem (seg_rom RSEGS)) model)
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
  assert (FC2 : file_clean mem1 0x201e0 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (SP1 : stdout_pending mem1 wb wp bufp bufsz rp1 can pending).
  { constructor; zaddr_goal; try assumption.
    1-9: (apply TR; [assumption | cbn; lia ..]).
    - apply TR; [assumption | lia ..].
    - split; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_flush fx o17_reloc o17_code o17_sites o17_data o17_rw
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
  realizes RSEGS (mkCfg (mkst regs (0x162cc : word) mem (seg_rom RSEGS)) model)
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
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x162cc) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending PRE.
  replace (Z_to_bv 64 0x162cc) with (0x162cc : word) by (apply bv_eq; reflexivity).
  exact (ref_exit regs mem model code pending PRE).
Qed.
End VP5.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End O17Exit.
