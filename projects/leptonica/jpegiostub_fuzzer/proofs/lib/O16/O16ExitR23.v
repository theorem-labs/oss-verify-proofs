(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.jpegiostub_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.CliDriver Require Import LibWritevG.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require Import LibAtomic.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Reloc Require Import Reloc RelocKit.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Musl Require Import MuslTac.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Musl Require StdioDefs Exit.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16 Require Import O16Kit O16_code_exitpath.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module O16Exit.
Import O16Kit.O16ExitBase.
Import O16Kit.O16StdioDefs.
Import O16Kit.O16Reloc.
Import O16Kit.O16RelocCode.
Import O16Kit.O16RelocSites.
Import O16Kit.O16RelocImg.
Import O16Kit.O16RelocMusl.

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
    (Z_to_bv 64 0x4fdb0) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x1595c)))
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
  rdn RSEGS mem (Z_to_bv 64 0x4fdb0) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x4fddb) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x158f8 : word) mem rom)
                 (mkst regs' (0x15740 : word)
                       (mem_wA mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 64)
    /\ getr regs' 8 = Z_to_bv 64 0x4fb94
    /\ getr regs' 18 = Z_to_bv 64 0x4fb90.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl.
  unfold mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepn F_158f8 D_158f8. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_158fc D_158fc (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_15900 D_15900 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_15904 D_15904.
    stepn F_15908 D_15908. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_1590c D_1590c (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_15910 D_15910.
    stepn F_15914 D_15914.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_15918 | reflexivity | exact D_15918
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_1591c | reflexivity | exact D_1591c | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_15920 | reflexivity | exact D_15920
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_15924 D_15924 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_15928 D_15928.
    (* [comment removed for export] *)
    stepb_ft F_1592c D_1592c ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_15930 D_15930 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_15954 D_15954. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_15958 D_15958.
    (* [comment removed for export] *)
    stepn F_15714 D_15714. sp_renorm.
    stepST F_15718 D_15718 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x1595c) ltac:(sok_stack SOK).
    stepST F_1571c D_1571c (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_15720 D_15720 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_15724 D_15724 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_15728 D_15728 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_1572c D_1572c.
    stepn F_15730 D_15730.
    stepn F_15734 D_15734.
    stepn F_15738 D_15738.
    stepn F_1573c D_1573c.
    (* [comment removed for export] *)
    stepn F_1d334 D_1d334.
    stepLB0 F_1d338 D_1d338.
    stepb_tk F_1d33c D_1d33c ltac:(cond_compute).
    stepretL F_1d52c D_1d52c (0x15740 : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wN (m : word -> option byte) := wbytes m (Z_to_bv 64 0x4fb90) [Z_to_bv 8 1].

Section VN.
  Context {fx : FPState}.
Lemma wN : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x4fb94 -> getr regs 18 = Z_to_bv 64 0x4fb90 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x4fba0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x4fb94) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x15740 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0x1595c : word) (mem_wN (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Malock.
  unfold mem_wN, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_15740 D_15740 (Z_to_bv 64 0).
    stepb_tk F_15744 D_15744 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_157b4 D_157b4.
    stepST F_157b8 D_157b8 (Z_to_bv 64 0x4fb90) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_157bc D_157bc. rewrite Hs0.
    (* [comment removed for export] *)
    stepLD8 F_157c0 D_157c0 (Z_to_bv 64 0x1595c).
    stepLD8 F_157c4 D_157c4 code.
    stepLD8 F_157c8 D_157c8 s1v.
    stepLD8 F_157cc D_157cc s2v.
    stepLD8 F_157d0 D_157d0 s3v.
    stepn F_157d4 D_157d4. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_157d8 D_157d8.
    stepLW F_1d5bc D_1d5bc 0%Z.
    stepb_ft F_1d5c0 D_1d5c0 ltac:(cond_compute).
    stepretL F_1d5c4 D_1d5c4 (0x1595c : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wO (m : word -> option byte) :=
  wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 0x4fb98) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x4fb98) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0x4fb98) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x4fba0) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x4fb90) [Z_to_bv 8 1].

Section VO.
  Context {fx : FPState}.
Lemma wO : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x4fb94 -> getr regs 18 = Z_to_bv 64 0x4fb90 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x4fba0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x4fba8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x4fb98) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
  rdn RSEGS mem (Z_to_bv 64 0x4fba8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x4fbb0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x158a4)) ->
  rdn RSEGS mem (Z_to_bv 64 0x4fcb0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13604)) ->
  rdn RSEGS mem (Z_to_bv 64 0x2fa54) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x4fb94) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x4fddb) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x15740 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0x1595c : word) (mem_wO (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Mslot Mnext Mf0 Ma0 Mcb Malock Mnl.
  unfold mem_wO, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_15740 D_15740 (Z_to_bv 64 0x4fba8).
    stepb_ft F_15744 D_15744 ltac:(cond_compute).
    stepLW F_15748 D_15748 1%Z.
    stepn F_1574c D_1574c.
    (* [comment removed for export] *)
    stepn F_15764 D_15764.
    stepST F_15768 D_15768 (Z_to_bv 64 0x4fb98) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_1576c D_1576c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_15770 D_15770 (Z_to_bv 64 0x4fba8).
    stepn F_15774 D_15774.
    stepn F_15778 D_15778.
    stepLD8 F_1577c D_1577c (Z_to_bv 64 0x158a4).
    stepLD8 F_15780 D_15780 (Z_to_bv 64 0x13604).
    (* [comment removed for export] *)
    stepn F_15784 D_15784. rewrite Hs0.
    stepn F_15788 D_15788.
    stepLW F_1d5bc D_1d5bc 0%Z.
    stepb_ft F_1d5c0 D_1d5c0 ltac:(cond_compute).
    stepretL F_1d5c4 D_1d5c4 (0x1578c : word).
    (* [comment removed for export] *)
    stepn F_1578c D_1578c.
    stepretL F_15790 D_15790 (0x158a4 : word).
    stepretL F_158a4 D_158a4 (0x13604 : word).
    (* [comment removed for export] *)
    stepn F_13604 D_13604.
    stepLBU F_13608 D_13608 (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_1360c D_1360c ltac:(cond_compute).
    stepretL F_13610 D_13610 (0x15794 : word).
    (* [comment removed for export] *)
    stepn F_15794 D_15794.
    stepn F_15798 D_15798.
    stepn F_1d334 D_1d334.
    stepLB0 F_1d338 D_1d338.
    stepb_tk F_1d33c D_1d33c ltac:(cond_compute).
    stepretL F_1d52c D_1d52c (0x1579c : word).
    (* [comment removed for export] *)
    stepLW F_1579c D_1579c 0%Z.
    stepn F_157a0 D_157a0.
    stepST F_157a4 D_157a4 (Z_to_bv 64 0x4fb98) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_157a8 D_157a8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_157ac D_157ac (Z_to_bv 64 0x4fba8).
    stepn F_157b0 D_157b0.
    stepLD8 F_15750 D_15750 (Z_to_bv 64 0).
    stepn F_15754 D_15754.
    stepST F_15758 D_15758 (Z_to_bv 64 0x4fb98) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_1575c D_1575c (Z_to_bv 64 0x4fba0) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_15760 D_15760 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_157b4 D_157b4.
    stepST F_157b8 D_157b8 (Z_to_bv 64 0x4fb90) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_157bc D_157bc.
    (* [comment removed for export] *)
    stepLD8 F_157c0 D_157c0 (Z_to_bv 64 0x1595c).
    stepLD8 F_157c4 D_157c4 code.
    stepLD8 F_157c8 D_157c8 s1v.
    stepLD8 F_157cc D_157cc s2v.
    stepLD8 F_157d0 D_157d0 s3v.
    stepn F_157d4 D_157d4. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_157d8 D_157d8.
    stepLW F_1d5bc D_1d5bc 0%Z.
    stepb_ft F_1d5c0 D_1d5c0 ltac:(cond_compute).
    stepretL F_1d5c4 D_1d5c4 (0x1595c : word).
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
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x15960)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x158dc)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x1e710)))
    (Z_to_bv 64 0x1fa48) [Z_to_bv 8 1].

Section V2R.
  Context {fx : FPState}.
Lemma w2R : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x1e7b8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1e718)) ->
  rdn RSEGS mem (Z_to_bv 64 0x1e7c0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1e710)) ->
  rdn RSEGS mem (Z_to_bv 64 0x1e710) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1314c)) ->
  rdn RSEGS mem (Z_to_bv 64 0x1fa48) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x1e758) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x157dc)) ->
  rdn RSEGS mem (Z_to_bv 64 0x1e760) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x1f7c8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1f7c8)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x1595c : word) mem rom)
                 (mkst regs' (0x17ac0 : word) (mem_w2R mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x15964.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mg2 Mdso.
  unfold mem_w2R. eexists. split.
  - (* [comment removed for export] *)
    stepn F_1595c D_1595c.
    stepn F_158ac D_158ac. rewrite Hsp. sp_renorm.
    stepST F_158b0 D_158b0 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x15960) ltac:(sok_stack SOK).
    stepST F_158b4 D_158b4 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_158b8 D_158b8 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_158bc D_158bc.
    stepn F_158c0 D_158c0.
    stepLD8 F_158c4 D_158c4 (Z_to_bv 64 0x1e718).
    stepLD8 F_158c8 D_158c8 (Z_to_bv 64 0x1e710).
    (* [comment removed for export] *)
    stepb_ft F_158cc D_158cc ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_158d0 D_158d0 (Z_to_bv 64 0x1314c).
    stepn F_158d4 D_158d4.
    stepretL F_158d8 D_158d8 (0x1314c : word).
    (* [comment removed for export] *)
    stepn F_1314c D_1314c. sp_renorm.
    stepST F_13150 D_13150 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x158dc) ltac:(sok_stack SOK).
    stepST F_13154 D_13154 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x1e710) ltac:(sok_stack SOK).
    stepn F_13158 D_13158.
    stepn F_1315c D_1315c.
    stepn F_13160 D_13160.
    (* [comment removed for export] *)
    stepLBU F_13164 D_13164 (Z_to_bv 8 0) ltac:(rewrite ?v_addi_0; rdn_by Mcomp).
    stepn F_13168 D_13168.
    stepb_tk F_1316c D_1316c ltac:(cond_compute).
    stepn F_13178 D_13178.
    stepn F_1317c D_1317c.
    stepn F_13180 D_13180.
    (* [comment removed for export] *)
    stepST F_13184 D_13184 (Z_to_bv 64 0x1fa48) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_13188 D_13188.
    stepLD8 F_1318c D_1318c (Z_to_bv 64 0x157dc).
    stepb_ft F_13190 D_13190 ltac:(cond_compute).
    stepn F_13194 D_13194.
    stepn F_13198 D_13198.
    stepn F_1319c D_1319c.
    stepLD8 F_131a0 D_131a0 (Z_to_bv 64 0x1f7c8).
    stepn F_131a4 D_131a4.
    stepretL F_157dc D_157dc (0x131a8 : word).
    stepn F_131a8 D_131a8.
    (* [comment removed for export] *)
    stepn F_131ac D_131ac.
    stepLD8 F_131b0 D_131b0 (Z_to_bv 64 0).
    stepb_tk F_131b4 D_131b4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_131cc D_131cc (Z_to_bv 64 0x158dc).
    stepLD8 F_131d0 D_131d0 (Z_to_bv 64 0x1e710).
    stepn F_131d4 D_131d4. sp_renorm.
    stepretL F_131d8 D_131d8 (0x158dc : word).
    (* [comment removed for export] *)
    stepn F_158dc D_158dc.
    stepb_ft F_158e0 D_158e0 ltac:(cond_compute).
    stepLD8 F_158e4 D_158e4 (Z_to_bv 64 0x15960).
    stepLD8 F_158e8 D_158e8 code.
    stepLD8 F_158ec D_158ec s1v.
    stepn F_158f0 D_158f0. sp_renorm.
    (* [comment removed for export] *)
    stepn F_158f4 D_158f4.
    stepretL F_158a8 D_158a8 (0x15960 : word).
    stepn F_15960 D_15960.
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
    msteps RSEGS (mkst regs (0x158f8 : word) mem rom) (mkst regs' (0x17ac0 : word) mem' rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x15964
    /\ store_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true
    /\ (forall (a : Z) n bs, rdn RSEGS mem (Z_to_bv 64 a) n = Some bs ->
          (0 <= a)%Z -> (a + Z.of_nat n <= 0x51000)%Z ->
          (a + Z.of_nat n <= 0x1fa48 \/ 0x1fa49 <= a)%Z ->
          (a + Z.of_nat n <= 0x4fb90 \/ 0x4fba8 <= a)%Z ->
          (a + Z.of_nat n <= 0x4fdb0 \/ 0x4fdb4 <= a)%Z ->
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
  file_clean mem 0x1f900 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0x158f8 : word) mem (seg_rom RSEGS)) model)
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
  assert (FC1 : file_clean mem1 0x1f900 wp1 rp1).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (FC2 : file_clean mem1 0x1f810 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_clean fx o16_reloc o16_code o16_sites o16_data o16_rw
             regs1 mem1 model sp code wp1 rp1 wp2 rp2 Rsp Rs0 Rra Esplo Esphi SOK1 G1 FC1 FC2 Hh Hlazy).
Qed.
End VP1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stdout_pending_G : forall mem wb wp bufp bufsz rp1 can pending,
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  @StdioDefs.stdout_pending o16_reloc mem wb wp bufp bufsz rp1 can pending.
Proof.
  intros mem wb wp bufp bufsz rp1 can pending [f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14].
  exact (@StdioDefs.Build_stdout_pending o16_reloc mem wb wp bufp bufsz rp1 can pending
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
  realizes RSEGS (mkCfg (mkst regs (0x158f8 : word) mem (seg_rom RSEGS)) model)
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
  assert (FC2 : file_clean mem1 0x1f810 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (SP1 : stdout_pending mem1 wb wp bufp bufsz rp1 can pending).
  { constructor; zaddr_goal; try assumption.
    1-9: (apply TR; [assumption | cbn; lia ..]).
    - apply TR; [assumption | lia ..].
    - split; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_flush fx o16_reloc o16_code o16_sites o16_data o16_rw
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
  realizes RSEGS (mkCfg (mkst regs (0x158f8 : word) mem (seg_rom RSEGS)) model)
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
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x158f8) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending PRE.
  replace (Z_to_bv 64 0x158f8) with (0x158f8 : word) by (apply bv_eq; reflexivity).
  exact (ref_exit regs mem model code pending PRE).
Qed.
End VP5.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End O16Exit.
