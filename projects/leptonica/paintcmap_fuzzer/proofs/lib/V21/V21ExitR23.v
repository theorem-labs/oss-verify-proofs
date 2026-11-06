(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.paintcmap_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.CliDriver Require Import LibWritevG.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require Import LibAtomic.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Reloc Require Import Reloc RelocKit.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Musl Require Import MuslTac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Musl Require StdioDefs Exit.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require Import V21Kit V21_code_exitpath.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module V21Exit.
Import V21Kit.V21ExitBase.
Import V21Kit.V21StdioDefs.
Import V21Kit.V21Reloc.
Import V21Kit.V21RelocCode.
Import V21Kit.V21RelocSites.
Import V21Kit.V21RelocImg.
Import V21Kit.V21RelocMusl.

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
    (Z_to_bv 64 0x52480) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x18038)))
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
  rdn RSEGS mem (Z_to_bv 64 0x52480) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x524ab) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x17fd4 : word) mem rom)
                 (mkst regs' (0x17e1c : word)
                       (mem_wA mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 64)
    /\ getr regs' 8 = Z_to_bv 64 0x52264
    /\ getr regs' 18 = Z_to_bv 64 0x52260.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl.
  unfold mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepn F_17fd4 D_17fd4. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_17fd8 D_17fd8 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_17fdc D_17fdc (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_17fe0 D_17fe0.
    stepn F_17fe4 D_17fe4. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_17fe8 D_17fe8 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_17fec D_17fec.
    stepn F_17ff0 D_17ff0.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_17ff4 | reflexivity | exact D_17ff4
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_17ff8 | reflexivity | exact D_17ff8 | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_17ffc | reflexivity | exact D_17ffc
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_18000 D_18000 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_18004 D_18004.
    (* [comment removed for export] *)
    stepb_ft F_18008 D_18008 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_1800c D_1800c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_18030 D_18030. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_18034 D_18034.
    (* [comment removed for export] *)
    stepn F_17df0 D_17df0. sp_renorm.
    stepST F_17df4 D_17df4 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x18038) ltac:(sok_stack SOK).
    stepST F_17df8 D_17df8 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_17dfc D_17dfc (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_17e00 D_17e00 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_17e04 D_17e04 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_17e08 D_17e08.
    stepn F_17e0c D_17e0c.
    stepn F_17e10 D_17e10.
    stepn F_17e14 D_17e14.
    stepn F_17e18 D_17e18.
    (* [comment removed for export] *)
    stepn F_1fa10 D_1fa10.
    stepLB0 F_1fa14 D_1fa14.
    stepb_tk F_1fa18 D_1fa18 ltac:(cond_compute).
    stepretL F_1fc08 D_1fc08 (0x17e1c : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wN (m : word -> option byte) := wbytes m (Z_to_bv 64 0x52260) [Z_to_bv 8 1].

Section VN.
  Context {fx : FPState}.
Lemma wN : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x52264 -> getr regs 18 = Z_to_bv 64 0x52260 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x52270) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x52264) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x17e1c : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0x18038 : word) (mem_wN (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Malock.
  unfold mem_wN, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_17e1c D_17e1c (Z_to_bv 64 0).
    stepb_tk F_17e20 D_17e20 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_17e90 D_17e90.
    stepST F_17e94 D_17e94 (Z_to_bv 64 0x52260) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_17e98 D_17e98. rewrite Hs0.
    (* [comment removed for export] *)
    stepLD8 F_17e9c D_17e9c (Z_to_bv 64 0x18038).
    stepLD8 F_17ea0 D_17ea0 code.
    stepLD8 F_17ea4 D_17ea4 s1v.
    stepLD8 F_17ea8 D_17ea8 s2v.
    stepLD8 F_17eac D_17eac s3v.
    stepn F_17eb0 D_17eb0. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_17eb4 D_17eb4.
    stepLW F_1fc98 D_1fc98 0%Z.
    stepb_ft F_1fc9c D_1fc9c ltac:(cond_compute).
    stepretL F_1fca0 D_1fca0 (0x18038 : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wO (m : word -> option byte) :=
  wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 0x52268) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x52268) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0x52268) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x52270) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x52260) [Z_to_bv 8 1].

Section VO.
  Context {fx : FPState}.
Lemma wO : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x52264 -> getr regs 18 = Z_to_bv 64 0x52260 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x52270) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x52278)) ->
  rdn RSEGS mem (Z_to_bv 64 0x52268) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
  rdn RSEGS mem (Z_to_bv 64 0x52278) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x52280) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x17f80)) ->
  rdn RSEGS mem (Z_to_bv 64 0x52380) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13cd0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x32124) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x52264) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x524ab) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x17e1c : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0x18038 : word) (mem_wO (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Mslot Mnext Mf0 Ma0 Mcb Malock Mnl.
  unfold mem_wO, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_17e1c D_17e1c (Z_to_bv 64 0x52278).
    stepb_ft F_17e20 D_17e20 ltac:(cond_compute).
    stepLW F_17e24 D_17e24 1%Z.
    stepn F_17e28 D_17e28.
    (* [comment removed for export] *)
    stepn F_17e40 D_17e40.
    stepST F_17e44 D_17e44 (Z_to_bv 64 0x52268) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_17e48 D_17e48 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_17e4c D_17e4c (Z_to_bv 64 0x52278).
    stepn F_17e50 D_17e50.
    stepn F_17e54 D_17e54.
    stepLD8 F_17e58 D_17e58 (Z_to_bv 64 0x17f80).
    stepLD8 F_17e5c D_17e5c (Z_to_bv 64 0x13cd0).
    (* [comment removed for export] *)
    stepn F_17e60 D_17e60. rewrite Hs0.
    stepn F_17e64 D_17e64.
    stepLW F_1fc98 D_1fc98 0%Z.
    stepb_ft F_1fc9c D_1fc9c ltac:(cond_compute).
    stepretL F_1fca0 D_1fca0 (0x17e68 : word).
    (* [comment removed for export] *)
    stepn F_17e68 D_17e68.
    stepretL F_17e6c D_17e6c (0x17f80 : word).
    stepretL F_17f80 D_17f80 (0x13cd0 : word).
    (* [comment removed for export] *)
    stepn F_13cd0 D_13cd0.
    stepLBU F_13cd4 D_13cd4 (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_13cd8 D_13cd8 ltac:(cond_compute).
    stepretL F_13cdc D_13cdc (0x17e70 : word).
    (* [comment removed for export] *)
    stepn F_17e70 D_17e70.
    stepn F_17e74 D_17e74.
    stepn F_1fa10 D_1fa10.
    stepLB0 F_1fa14 D_1fa14.
    stepb_tk F_1fa18 D_1fa18 ltac:(cond_compute).
    stepretL F_1fc08 D_1fc08 (0x17e78 : word).
    (* [comment removed for export] *)
    stepLW F_17e78 D_17e78 0%Z.
    stepn F_17e7c D_17e7c.
    stepST F_17e80 D_17e80 (Z_to_bv 64 0x52268) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_17e84 D_17e84 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_17e88 D_17e88 (Z_to_bv 64 0x52278).
    stepn F_17e8c D_17e8c.
    stepLD8 F_17e2c D_17e2c (Z_to_bv 64 0).
    stepn F_17e30 D_17e30.
    stepST F_17e34 D_17e34 (Z_to_bv 64 0x52268) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_17e38 D_17e38 (Z_to_bv 64 0x52270) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_17e3c D_17e3c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_17e90 D_17e90.
    stepST F_17e94 D_17e94 (Z_to_bv 64 0x52260) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_17e98 D_17e98.
    (* [comment removed for export] *)
    stepLD8 F_17e9c D_17e9c (Z_to_bv 64 0x18038).
    stepLD8 F_17ea0 D_17ea0 code.
    stepLD8 F_17ea4 D_17ea4 s1v.
    stepLD8 F_17ea8 D_17ea8 s2v.
    stepLD8 F_17eac D_17eac s3v.
    stepn F_17eb0 D_17eb0. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_17eb4 D_17eb4.
    stepLW F_1fc98 D_1fc98 0%Z.
    stepb_ft F_1fc9c D_1fc9c ltac:(cond_compute).
    stepretL F_1fca0 D_1fca0 (0x18038 : word).
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
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x1803c)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x17fb8)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x20de8)))
    (Z_to_bv 64 0x22118) [Z_to_bv 8 1].

Section V2R.
  Context {fx : FPState}.
Lemma w2R : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x20e90) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x20df0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x20e98) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x20de8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x20de8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13818)) ->
  rdn RSEGS mem (Z_to_bv 64 0x22118) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x20e30) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x17eb8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x20e38) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x21ea0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x21ea0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x18038 : word) mem rom)
                 (mkst regs' (0x1a19c : word) (mem_w2R mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x18040.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mg2 Mdso.
  unfold mem_w2R. eexists. split.
  - (* [comment removed for export] *)
    stepn F_18038 D_18038.
    stepn F_17f88 D_17f88. rewrite Hsp. sp_renorm.
    stepST F_17f8c D_17f8c (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x1803c) ltac:(sok_stack SOK).
    stepST F_17f90 D_17f90 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_17f94 D_17f94 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_17f98 D_17f98.
    stepn F_17f9c D_17f9c.
    stepLD8 F_17fa0 D_17fa0 (Z_to_bv 64 0x20df0).
    stepLD8 F_17fa4 D_17fa4 (Z_to_bv 64 0x20de8).
    (* [comment removed for export] *)
    stepb_ft F_17fa8 D_17fa8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_17fac D_17fac (Z_to_bv 64 0x13818).
    stepn F_17fb0 D_17fb0.
    stepretL F_17fb4 D_17fb4 (0x13818 : word).
    (* [comment removed for export] *)
    stepn F_13818 D_13818. sp_renorm.
    stepST F_1381c D_1381c (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x17fb8) ltac:(sok_stack SOK).
    stepST F_13820 D_13820 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x20de8) ltac:(sok_stack SOK).
    stepn F_13824 D_13824.
    stepn F_13828 D_13828.
    stepn F_1382c D_1382c.
    (* [comment removed for export] *)
    stepLBU F_13830 D_13830 (Z_to_bv 8 0) ltac:(rewrite ?v_addi_0; rdn_by Mcomp).
    stepn F_13834 D_13834.
    stepb_tk F_13838 D_13838 ltac:(cond_compute).
    stepn F_13844 D_13844.
    stepn F_13848 D_13848.
    stepn F_1384c D_1384c.
    (* [comment removed for export] *)
    stepST F_13850 D_13850 (Z_to_bv 64 0x22118) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_13854 D_13854.
    stepLD8 F_13858 D_13858 (Z_to_bv 64 0x17eb8).
    stepb_ft F_1385c D_1385c ltac:(cond_compute).
    stepn F_13860 D_13860.
    stepn F_13864 D_13864.
    stepn F_13868 D_13868.
    stepLD8 F_1386c D_1386c (Z_to_bv 64 0x21ea0).
    stepn F_13870 D_13870.
    stepretL F_17eb8 D_17eb8 (0x13874 : word).
    stepn F_13874 D_13874.
    (* [comment removed for export] *)
    stepn F_13878 D_13878.
    stepLD8 F_1387c D_1387c (Z_to_bv 64 0).
    stepb_tk F_13880 D_13880 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_13898 D_13898 (Z_to_bv 64 0x17fb8).
    stepLD8 F_1389c D_1389c (Z_to_bv 64 0x20de8).
    stepn F_138a0 D_138a0. sp_renorm.
    stepretL F_138a4 D_138a4 (0x17fb8 : word).
    (* [comment removed for export] *)
    stepn F_17fb8 D_17fb8.
    stepb_ft F_17fbc D_17fbc ltac:(cond_compute).
    stepLD8 F_17fc0 D_17fc0 (Z_to_bv 64 0x1803c).
    stepLD8 F_17fc4 D_17fc4 code.
    stepLD8 F_17fc8 D_17fc8 s1v.
    stepn F_17fcc D_17fcc. sp_renorm.
    (* [comment removed for export] *)
    stepn F_17fd0 D_17fd0.
    stepretL F_17f84 D_17f84 (0x1803c : word).
    stepn F_1803c D_1803c.
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
    msteps RSEGS (mkst regs (0x17fd4 : word) mem rom) (mkst regs' (0x1a19c : word) mem' rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x18040
    /\ store_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true
    /\ (forall (a : Z) n bs, rdn RSEGS mem (Z_to_bv 64 a) n = Some bs ->
          (0 <= a)%Z -> (a + Z.of_nat n <= 0x53000)%Z ->
          (a + Z.of_nat n <= 0x22118 \/ 0x22119 <= a)%Z ->
          (a + Z.of_nat n <= 0x52260 \/ 0x52278 <= a)%Z ->
          (a + Z.of_nat n <= 0x52480 \/ 0x52484 <= a)%Z ->
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
  file_clean mem 0x21fd8 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0x17fd4 : word) mem (seg_rom RSEGS)) model)
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
  assert (FC1 : file_clean mem1 0x21fd8 wp1 rp1).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (FC2 : file_clean mem1 0x21ee8 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_clean fx v21_reloc v21_code v21_sites v21_data v21_rw
             regs1 mem1 model sp code wp1 rp1 wp2 rp2 Rsp Rs0 Rra Esplo Esphi SOK1 G1 FC1 FC2 Hh Hlazy).
Qed.
End VP1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stdout_pending_G : forall mem wb wp bufp bufsz rp1 can pending,
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  @StdioDefs.stdout_pending v21_reloc mem wb wp bufp bufsz rp1 can pending.
Proof.
  intros mem wb wp bufp bufsz rp1 can pending [f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14].
  exact (@StdioDefs.Build_stdout_pending v21_reloc mem wb wp bufp bufsz rp1 can pending
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
  realizes RSEGS (mkCfg (mkst regs (0x17fd4 : word) mem (seg_rom RSEGS)) model)
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
  assert (FC2 : file_clean mem1 0x21ee8 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (SP1 : stdout_pending mem1 wb wp bufp bufsz rp1 can pending).
  { constructor; zaddr_goal; try assumption.
    1-9: (apply TR; [assumption | cbn; lia ..]).
    - apply TR; [assumption | lia ..].
    - split; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_flush fx v21_reloc v21_code v21_sites v21_data v21_rw
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
  realizes RSEGS (mkCfg (mkst regs (0x17fd4 : word) mem (seg_rom RSEGS)) model)
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
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x17fd4) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending PRE.
  replace (Z_to_bv 64 0x17fd4) with (0x17fd4 : word) by (apply bv_eq; reflexivity).
  exact (ref_exit regs mem model code pending PRE).
Qed.
End VP5.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End V21Exit.
