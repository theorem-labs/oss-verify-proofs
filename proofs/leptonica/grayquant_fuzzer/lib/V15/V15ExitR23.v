(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim ExitSim ShapeAlg Nodes.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import LibWritevG.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import LibAtomic.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require WalksLib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Spec.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc Require Import Reloc RelocKit.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Musl Require Import MuslTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Musl Require StdioDefs Exit.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15Kit V15_code_exitpath.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module V15Exit.
Import V15Kit.V15ExitBase.
Import V15Kit.V15StdioDefs.
Import V15Kit.V15Reloc.
Import V15Kit.V15RelocCode.
Import V15Kit.V15RelocSites.
Import V15Kit.V15RelocImg.
Import V15Kit.V15RelocMusl.

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
    (Z_to_bv 64 0x65820) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x28780)))
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
  rdn RSEGS mem (Z_to_bv 64 0x65820) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x6584b) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x2871c : word) mem rom)
                 (mkst regs' (0x28564 : word)
                       (mem_wA mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 64)
    /\ getr regs' 8 = Z_to_bv 64 0x65604
    /\ getr regs' 18 = Z_to_bv 64 0x65600.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl.
  unfold mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepn F_2871c D_2871c. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_28720 D_28720 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_28724 D_28724 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_28728 D_28728.
    stepn F_2872c D_2872c. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_28730 D_28730 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_28734 D_28734.
    stepn F_28738 D_28738.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_2873c | reflexivity | exact D_2873c
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_28740 | reflexivity | exact D_28740 | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_28744 | reflexivity | exact D_28744
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_28748 D_28748 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_2874c D_2874c.
    (* [comment removed for export] *)
    stepb_ft F_28750 D_28750 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_28754 D_28754 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_28778 D_28778. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_2877c D_2877c.
    (* [comment removed for export] *)
    stepn F_28538 D_28538. sp_renorm.
    stepST F_2853c D_2853c (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x28780) ltac:(sok_stack SOK).
    stepST F_28540 D_28540 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_28544 D_28544 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_28548 D_28548 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_2854c D_2854c (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_28550 D_28550.
    stepn F_28554 D_28554.
    stepn F_28558 D_28558.
    stepn F_2855c D_2855c.
    stepn F_28560 D_28560.
    (* [comment removed for export] *)
    stepn F_32db0 D_32db0.
    stepLB0 F_32db4 D_32db4.
    stepb_tk F_32db8 D_32db8 ltac:(cond_compute).
    stepretL F_32fa8 D_32fa8 (0x28564 : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wN (m : word -> option byte) := wbytes m (Z_to_bv 64 0x65600) [Z_to_bv 8 1].

Section VN.
  Context {fx : FPState}.
Lemma wN : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x65604 -> getr regs 18 = Z_to_bv 64 0x65600 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x65610) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x65604) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x28564 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0x28780 : word) (mem_wN (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Malock.
  unfold mem_wN, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_28564 D_28564 (Z_to_bv 64 0).
    stepb_tk F_28568 D_28568 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_285d8 D_285d8.
    stepST F_285dc D_285dc (Z_to_bv 64 0x65600) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_285e0 D_285e0. rewrite Hs0.
    (* [comment removed for export] *)
    stepLD8 F_285e4 D_285e4 (Z_to_bv 64 0x28780).
    stepLD8 F_285e8 D_285e8 code.
    stepLD8 F_285ec D_285ec s1v.
    stepLD8 F_285f0 D_285f0 s2v.
    stepLD8 F_285f4 D_285f4 s3v.
    stepn F_285f8 D_285f8. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_285fc D_285fc.
    stepLW F_33038 D_33038 0%Z.
    stepb_ft F_3303c D_3303c ltac:(cond_compute).
    stepretL F_33040 D_33040 (0x28780 : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wO (m : word -> option byte) :=
  wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 0x65608) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x65608) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0x65608) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x65610) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x65600) [Z_to_bv 8 1].

Section VO.
  Context {fx : FPState}.
Lemma wO : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x65604 -> getr regs 18 = Z_to_bv 64 0x65600 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x65610) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x65618)) ->
  rdn RSEGS mem (Z_to_bv 64 0x65608) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
  rdn RSEGS mem (Z_to_bv 64 0x65618) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x65620) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x286c8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x65720) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x152d0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x454c4) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x65604) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x6584b) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x28564 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0x28780 : word) (mem_wO (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Mslot Mnext Mf0 Ma0 Mcb Malock Mnl.
  unfold mem_wO, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_28564 D_28564 (Z_to_bv 64 0x65618).
    stepb_ft F_28568 D_28568 ltac:(cond_compute).
    stepLW F_2856c D_2856c 1%Z.
    stepn F_28570 D_28570.
    (* [comment removed for export] *)
    stepn F_28588 D_28588.
    stepST F_2858c D_2858c (Z_to_bv 64 0x65608) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_28590 D_28590 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_28594 D_28594 (Z_to_bv 64 0x65618).
    stepn F_28598 D_28598.
    stepn F_2859c D_2859c.
    stepLD8 F_285a0 D_285a0 (Z_to_bv 64 0x286c8).
    stepLD8 F_285a4 D_285a4 (Z_to_bv 64 0x152d0).
    (* [comment removed for export] *)
    stepn F_285a8 D_285a8. rewrite Hs0.
    stepn F_285ac D_285ac.
    stepLW F_33038 D_33038 0%Z.
    stepb_ft F_3303c D_3303c ltac:(cond_compute).
    stepretL F_33040 D_33040 (0x285b0 : word).
    (* [comment removed for export] *)
    stepn F_285b0 D_285b0.
    stepretL F_285b4 D_285b4 (0x286c8 : word).
    stepretL F_286c8 D_286c8 (0x152d0 : word).
    (* [comment removed for export] *)
    stepn F_152d0 D_152d0.
    stepLBU F_152d4 D_152d4 (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_152d8 D_152d8 ltac:(cond_compute).
    stepretL F_152dc D_152dc (0x285b8 : word).
    (* [comment removed for export] *)
    stepn F_285b8 D_285b8.
    stepn F_285bc D_285bc.
    stepn F_32db0 D_32db0.
    stepLB0 F_32db4 D_32db4.
    stepb_tk F_32db8 D_32db8 ltac:(cond_compute).
    stepretL F_32fa8 D_32fa8 (0x285c0 : word).
    (* [comment removed for export] *)
    stepLW F_285c0 D_285c0 0%Z.
    stepn F_285c4 D_285c4.
    stepST F_285c8 D_285c8 (Z_to_bv 64 0x65608) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_285cc D_285cc ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_285d0 D_285d0 (Z_to_bv 64 0x65618).
    stepn F_285d4 D_285d4.
    stepLD8 F_28574 D_28574 (Z_to_bv 64 0).
    stepn F_28578 D_28578.
    stepST F_2857c D_2857c (Z_to_bv 64 0x65608) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_28580 D_28580 (Z_to_bv 64 0x65610) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_28584 D_28584 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_285d8 D_285d8.
    stepST F_285dc D_285dc (Z_to_bv 64 0x65600) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_285e0 D_285e0.
    (* [comment removed for export] *)
    stepLD8 F_285e4 D_285e4 (Z_to_bv 64 0x28780).
    stepLD8 F_285e8 D_285e8 code.
    stepLD8 F_285ec D_285ec s1v.
    stepLD8 F_285f0 D_285f0 s2v.
    stepLD8 F_285f4 D_285f4 s3v.
    stepn F_285f8 D_285f8. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_285fc D_285fc.
    stepLW F_33038 D_33038 0%Z.
    stepb_ft F_3303c D_3303c ltac:(cond_compute).
    stepretL F_33040 D_33040 (0x28780 : word).
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
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x28784)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x28700)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x34188)))
    (Z_to_bv 64 0x354b8) [Z_to_bv 8 1].

Section V2R.
  Context {fx : FPState}.
Lemma w2R : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x34230) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x34190)) ->
  rdn RSEGS mem (Z_to_bv 64 0x34238) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x34188)) ->
  rdn RSEGS mem (Z_to_bv 64 0x34188) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x14e18)) ->
  rdn RSEGS mem (Z_to_bv 64 0x354b8) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x341d0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x28600)) ->
  rdn RSEGS mem (Z_to_bv 64 0x341d8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x35240) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x35240)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x28780 : word) mem rom)
                 (mkst regs' (0x2aa04 : word) (mem_w2R mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x28788.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mg2 Mdso.
  unfold mem_w2R. eexists. split.
  - (* [comment removed for export] *)
    stepn F_28780 D_28780.
    stepn F_286d0 D_286d0. rewrite Hsp. sp_renorm.
    stepST F_286d4 D_286d4 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x28784) ltac:(sok_stack SOK).
    stepST F_286d8 D_286d8 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_286dc D_286dc (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_286e0 D_286e0.
    stepn F_286e4 D_286e4.
    stepLD8 F_286e8 D_286e8 (Z_to_bv 64 0x34190).
    stepLD8 F_286ec D_286ec (Z_to_bv 64 0x34188).
    (* [comment removed for export] *)
    stepb_ft F_286f0 D_286f0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_286f4 D_286f4 (Z_to_bv 64 0x14e18).
    stepn F_286f8 D_286f8.
    stepretL F_286fc D_286fc (0x14e18 : word).
    (* [comment removed for export] *)
    stepn F_14e18 D_14e18. sp_renorm.
    stepST F_14e1c D_14e1c (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x28700) ltac:(sok_stack SOK).
    stepST F_14e20 D_14e20 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x34188) ltac:(sok_stack SOK).
    stepn F_14e24 D_14e24.
    stepn F_14e28 D_14e28.
    stepn F_14e2c D_14e2c.
    (* [comment removed for export] *)
    stepLBU F_14e30 D_14e30 (Z_to_bv 8 0) ltac:(rewrite ?v_addi_0; rdn_by Mcomp).
    stepn F_14e34 D_14e34.
    stepb_tk F_14e38 D_14e38 ltac:(cond_compute).
    stepn F_14e44 D_14e44.
    stepn F_14e48 D_14e48.
    stepn F_14e4c D_14e4c.
    (* [comment removed for export] *)
    stepST F_14e50 D_14e50 (Z_to_bv 64 0x354b8) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_14e54 D_14e54.
    stepLD8 F_14e58 D_14e58 (Z_to_bv 64 0x28600).
    stepb_ft F_14e5c D_14e5c ltac:(cond_compute).
    stepn F_14e60 D_14e60.
    stepn F_14e64 D_14e64.
    stepn F_14e68 D_14e68.
    stepLD8 F_14e6c D_14e6c (Z_to_bv 64 0x35240).
    stepn F_14e70 D_14e70.
    stepretL F_28600 D_28600 (0x14e74 : word).
    stepn F_14e74 D_14e74.
    (* [comment removed for export] *)
    stepn F_14e78 D_14e78.
    stepLD8 F_14e7c D_14e7c (Z_to_bv 64 0).
    stepb_tk F_14e80 D_14e80 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_14e98 D_14e98 (Z_to_bv 64 0x28700).
    stepLD8 F_14e9c D_14e9c (Z_to_bv 64 0x34188).
    stepn F_14ea0 D_14ea0. sp_renorm.
    stepretL F_14ea4 D_14ea4 (0x28700 : word).
    (* [comment removed for export] *)
    stepn F_28700 D_28700.
    stepb_ft F_28704 D_28704 ltac:(cond_compute).
    stepLD8 F_28708 D_28708 (Z_to_bv 64 0x28784).
    stepLD8 F_2870c D_2870c code.
    stepLD8 F_28710 D_28710 s1v.
    stepn F_28714 D_28714. sp_renorm.
    (* [comment removed for export] *)
    stepn F_28718 D_28718.
    stepretL F_286cc D_286cc (0x28784 : word).
    stepn F_28784 D_28784.
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
    msteps RSEGS (mkst regs (0x2871c : word) mem rom) (mkst regs' (0x2aa04 : word) mem' rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x28788
    /\ store_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true
    /\ (forall (a : Z) n bs, rdn RSEGS mem (Z_to_bv 64 a) n = Some bs ->
          (0 <= a)%Z -> (a + Z.of_nat n <= 0x67000)%Z ->
          (a + Z.of_nat n <= 0x354b8 \/ 0x354b9 <= a)%Z ->
          (a + Z.of_nat n <= 0x65600 \/ 0x65618 <= a)%Z ->
          (a + Z.of_nat n <= 0x65820 \/ 0x65824 <= a)%Z ->
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
  file_clean mem 0x35378 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0x2871c : word) mem (seg_rom RSEGS)) model)
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
  assert (FC1 : file_clean mem1 0x35378 wp1 rp1).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (FC2 : file_clean mem1 0x35288 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_clean fx v15_reloc v15_code v15_sites v15_data v15_rw
             regs1 mem1 model sp code wp1 rp1 wp2 rp2 Rsp Rs0 Rra Esplo Esphi SOK1 G1 FC1 FC2 Hh Hlazy).
Qed.
End VP1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stdout_pending_G : forall mem wb wp bufp bufsz rp1 can pending,
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  @StdioDefs.stdout_pending v15_reloc mem wb wp bufp bufsz rp1 can pending.
Proof.
  intros mem wb wp bufp bufsz rp1 can pending [f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14].
  exact (@StdioDefs.Build_stdout_pending v15_reloc mem wb wp bufp bufsz rp1 can pending
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
  realizes RSEGS (mkCfg (mkst regs (0x2871c : word) mem (seg_rom RSEGS)) model)
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
  assert (FC2 : file_clean mem1 0x35288 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (SP1 : stdout_pending mem1 wb wp bufp bufsz rp1 can pending).
  { constructor; zaddr_goal; try assumption.
    1-9: (apply TR; [assumption | cbn; lia ..]).
    - apply TR; [assumption | lia ..].
    - split; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_flush fx v15_reloc v15_code v15_sites v15_data v15_rw
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
  realizes RSEGS (mkCfg (mkst regs (0x2871c : word) mem (seg_rom RSEGS)) model)
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
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x2871c) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending PRE.
  replace (Z_to_bv 64 0x2871c) with (0x2871c : word) by (apply bv_eq; reflexivity).
  exact (ref_exit regs mem model code pending PRE).
Qed.
End VP5.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End V15Exit.
