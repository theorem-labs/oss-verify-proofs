(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver Require Import LibWritevG.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require Import LibAtomic.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc Require Import Reloc RelocKit.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Musl Require Import MuslTac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Musl Require StdioDefs Exit.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.V9 Require Import V9Kit V9_code_exitpath.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module V9Exit.
Import V9Kit.V9ExitBase.
Import V9Kit.V9StdioDefs.
Import V9Kit.V9Reloc.
Import V9Kit.V9RelocCode.
Import V9Kit.V9RelocSites.
Import V9Kit.V9RelocImg.
Import V9Kit.V9RelocMusl.

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
    (Z_to_bv 64 0x12aac0) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0xe22e4)))
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
  rdn RSEGS mem (Z_to_bv 64 0x12aac0) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x12aaeb) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0xe2280 : word) mem rom)
                 (mkst regs' (0xe20c8 : word)
                       (mem_wA mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 64)
    /\ getr regs' 8 = Z_to_bv 64 0x12a8a4
    /\ getr regs' 18 = Z_to_bv 64 0x12a8a0.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl.
  unfold mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepn F_e2238 D_e2238. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_e223c D_e223c (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_e2240 D_e2240 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_e2244 D_e2244.
    stepn F_e2248 D_e2248. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_e224c D_e224c (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_e2250 D_e2250.
    stepn F_e2254 D_e2254.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_e2258 | reflexivity | exact D_e2258
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_e225c | reflexivity | exact D_e225c | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_e2260 | reflexivity | exact D_e2260
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_e2264 D_e2264 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_e2268 D_e2268.
    (* [comment removed for export] *)
    stepb_ft F_e226c D_e226c ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_e2270 D_e2270 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_e2294 D_e2294. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_e2298 D_e2298.
    (* [comment removed for export] *)
    stepn F_e2054 D_e2054. sp_renorm.
    stepST F_e2058 D_e2058 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0xe22e4) ltac:(sok_stack SOK).
    stepST F_e205c D_e205c (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_e2060 D_e2060 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_e2064 D_e2064 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_e2068 D_e2068 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_e206c D_e206c.
    stepn F_e2070 D_e2070.
    stepn F_e2074 D_e2074.
    stepn F_e2078 D_e2078.
    stepn F_e207c D_e207c.
    (* [comment removed for export] *)
    stepn F_f15c4 D_f15c4.
    stepLB0 F_f15c8 D_f15c8.
    stepb_tk F_f15cc D_f15cc ltac:(cond_compute).
    stepretL F_f17bc D_f17bc (0xe20c8 : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wN (m : word -> option byte) := wbytes m (Z_to_bv 64 0x12a8a0) [Z_to_bv 8 1].

Section VN.
  Context {fx : FPState}.
Lemma wN : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x12a8a4 -> getr regs 18 = Z_to_bv 64 0x12a8a0 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x12a8b0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x12a8a4) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0xe20c8 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0xe22e4 : word) (mem_wN (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Malock.
  unfold mem_wN, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_e2080 D_e2080 (Z_to_bv 64 0).
    stepb_tk F_e2084 D_e2084 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_e20f4 D_e20f4.
    stepST F_e20f8 D_e20f8 (Z_to_bv 64 0x12a8a0) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_e20fc D_e20fc. rewrite Hs0.
    (* [comment removed for export] *)
    stepLD8 F_e2100 D_e2100 (Z_to_bv 64 0xe22e4).
    stepLD8 F_e2104 D_e2104 code.
    stepLD8 F_e2108 D_e2108 s1v.
    stepLD8 F_e210c D_e210c s2v.
    stepLD8 F_e2110 D_e2110 s3v.
    stepn F_e2114 D_e2114. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_e2118 D_e2118.
    stepLW F_f184c D_f184c 0%Z.
    stepb_ft F_f1850 D_f1850 ltac:(cond_compute).
    stepretL F_f1854 D_f1854 (0xe22e4 : word).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End VN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem_wO (m : word -> option byte) :=
  wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 0x12a8a8) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x12a8a8) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0x12a8a8) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x12a8b0) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x12a8a0) [Z_to_bv 8 1].

Section VO.
  Context {fx : FPState}.
Lemma wO : forall regs mem rom (sp ra s0v code s1v s2v s3v : word) (tid : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 64) ->
  getr regs 8 = Z_to_bv 64 0x12a8a4 -> getr regs 18 = Z_to_bv 64 0x12a8a0 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 0x12a8b0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12a8b8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x12a8a8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
  rdn RSEGS mem (Z_to_bv 64 0x12a8b8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x12a8c0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe222c)) ->
  rdn RSEGS mem (Z_to_bv 64 0x12a9c0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x5d0c8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x10a5a4) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x12a8a4) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x12aaeb) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0xe20c8 : word) (mem_wA mem sp ra s0v code s1v s2v s3v tid) rom)
                 (mkst regs' (0xe22e4 : word) (mem_wO (mem_wA mem sp ra s0v code s1v s2v s3v tid)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v.
Proof.
  intros regs mem rom sp ra s0v code s1v s2v s3v tid Hsp Hs0 Hs2 SPlo SPhi Mhead Mslot Mnext Mf0 Ma0 Mcb Malock Mnl.
  unfold mem_wO, mem_wA. eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_e2080 D_e2080 (Z_to_bv 64 0x12a8b8).
    stepb_ft F_e2084 D_e2084 ltac:(cond_compute).
    stepLW F_e2088 D_e2088 1%Z.
    stepn F_e208c D_e208c.
    (* [comment removed for export] *)
    stepn F_e20a4 D_e20a4.
    stepST F_e20a8 D_e20a8 (Z_to_bv 64 0x12a8a8) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_e20ac D_e20ac ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_e20b0 D_e20b0 (Z_to_bv 64 0x12a8b8).
    stepn F_e20b4 D_e20b4.
    stepn F_e20b8 D_e20b8.
    stepLD8 F_e20bc D_e20bc (Z_to_bv 64 0xe222c).
    stepLD8 F_e20c0 D_e20c0 (Z_to_bv 64 0x5d0c8).
    (* [comment removed for export] *)
    stepn F_e20c4 D_e20c4. rewrite Hs0.
    stepn F_e20c8 D_e20c8.
    stepLW F_f184c D_f184c 0%Z.
    stepb_ft F_f1850 D_f1850 ltac:(cond_compute).
    stepretL F_f1854 D_f1854 (0xe2114 : word).
    (* [comment removed for export] *)
    stepn F_e20cc D_e20cc.
    stepretL F_e20d0 D_e20d0 (0xe222c : word).
    stepretL F_e21e4 D_e21e4 (0x5d0c8 : word).
    (* [comment removed for export] *)
    stepn F_5d070 D_5d070.
    stepLBU F_5d074 D_5d074 (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_5d078 D_5d078 ltac:(cond_compute).
    stepretL F_5d07c D_5d07c (0xe211c : word).
    (* [comment removed for export] *)
    stepn F_e20d4 D_e20d4.
    stepn F_e20d8 D_e20d8.
    stepn F_f15c4 D_f15c4.
    stepLB0 F_f15c8 D_f15c8.
    stepb_tk F_f15cc D_f15cc ltac:(cond_compute).
    stepretL F_f17bc D_f17bc (0xe2124 : word).
    (* [comment removed for export] *)
    stepLW F_e20dc D_e20dc 0%Z.
    stepn F_e20e0 D_e20e0.
    stepST F_e20e4 D_e20e4 (Z_to_bv 64 0x12a8a8) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_e20e8 D_e20e8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_e20ec D_e20ec (Z_to_bv 64 0x12a8b8).
    stepn F_e20f0 D_e20f0.
    stepLD8 F_e2090 D_e2090 (Z_to_bv 64 0).
    stepn F_e2094 D_e2094.
    stepST F_e2098 D_e2098 (Z_to_bv 64 0x12a8a8) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_e209c D_e209c (Z_to_bv 64 0x12a8b0) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_e20a0 D_e20a0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_e20f4 D_e20f4.
    stepST F_e20f8 D_e20f8 (Z_to_bv 64 0x12a8a0) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_e20fc D_e20fc.
    (* [comment removed for export] *)
    stepLD8 F_e2100 D_e2100 (Z_to_bv 64 0xe22e4).
    stepLD8 F_e2104 D_e2104 code.
    stepLD8 F_e2108 D_e2108 s1v.
    stepLD8 F_e210c D_e210c s2v.
    stepLD8 F_e2110 D_e2110 s3v.
    stepn F_e2114 D_e2114. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepn F_e2118 D_e2118.
    stepLW F_f184c D_f184c 0%Z.
    stepb_ft F_f1850 D_f1850 ltac:(cond_compute).
    stepretL F_f1854 D_f1854 (0xe22e4 : word).
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
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0xe22e8)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0xe2264)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0xf5d48)))
    (Z_to_bv 64 0xfa598) [Z_to_bv 8 1].

Section V2R.
  Context {fx : FPState}.
Lemma w2R : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0xf92b0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xf5d50)) ->
  rdn RSEGS mem (Z_to_bv 64 0xf92b8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xf5d48)) ->
  rdn RSEGS mem (Z_to_bv 64 0xf5d48) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x5cc10)) ->
  rdn RSEGS mem (Z_to_bv 64 0xfa598) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0xf90f0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe2164)) ->
  rdn RSEGS mem (Z_to_bv 64 0xf90f8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0xfa2d8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xfa2d8)) ->
  exists regs',
    msteps RSEGS (mkst regs (0xe22e4 : word) mem rom)
                 (mkst regs' (0xe5fc0 : word) (mem_w2R mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0xe22ec.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mg2 Mdso.
  unfold mem_w2R. eexists. split.
  - (* [comment removed for export] *)
    stepn F_e229c D_e229c.
    stepn F_e21ec D_e21ec. rewrite Hsp. sp_renorm.
    stepST F_e21f0 D_e21f0 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0xe22e8) ltac:(sok_stack SOK).
    stepST F_e21f4 D_e21f4 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_e21f8 D_e21f8 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_e21fc D_e21fc.
    stepn F_e2200 D_e2200.
    stepLD8 F_e2204 D_e2204 (Z_to_bv 64 0xf5d50).
    stepLD8 F_e2208 D_e2208 (Z_to_bv 64 0xf5d48).
    (* [comment removed for export] *)
    stepb_ft F_e220c D_e220c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_e2210 D_e2210 (Z_to_bv 64 0x5cc10).
    stepn F_e2214 D_e2214.
    stepretL F_e2218 D_e2218 (0x5cc10 : word).
    (* [comment removed for export] *)
    stepn F_5cbb8 D_5cbb8. sp_renorm.
    stepST F_5cbbc D_5cbbc (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0xe2264) ltac:(sok_stack SOK).
    stepST F_5cbc0 D_5cbc0 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0xf5d48) ltac:(sok_stack SOK).
    stepn F_5cbc4 D_5cbc4.
    stepn F_5cbc8 D_5cbc8.
    stepn F_5cbcc D_5cbcc.
    (* [comment removed for export] *)
    stepLBU F_5cbd0 D_5cbd0 (Z_to_bv 8 0) ltac:(rewrite ?v_addi_0; rdn_by Mcomp).
    stepn F_5cbd4 D_5cbd4.
    stepb_tk F_5cbd8 D_5cbd8 ltac:(cond_compute).
    stepn F_5cbe4 D_5cbe4.
    stepn F_5cbe8 D_5cbe8.
    stepn F_5cbec D_5cbec.
    (* [comment removed for export] *)
    stepST F_5cbf0 D_5cbf0 (Z_to_bv 64 0xfa598) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_5cbf4 D_5cbf4.
    stepLD8 F_5cbf8 D_5cbf8 (Z_to_bv 64 0xe2164).
    stepb_ft F_5cbfc D_5cbfc ltac:(cond_compute).
    stepn F_5cc00 D_5cc00.
    stepn F_5cc04 D_5cc04.
    stepn F_5cc08 D_5cc08.
    stepLD8 F_5cc0c D_5cc0c (Z_to_bv 64 0xfa2d8).
    stepn F_5cc10 D_5cc10.
    stepretL F_e211c D_e211c (0x5cc6c : word).
    stepn F_5cc14 D_5cc14.
    (* [comment removed for export] *)
    stepn F_5cc18 D_5cc18.
    stepLD8 F_5cc1c D_5cc1c (Z_to_bv 64 0).
    stepb_tk F_5cc20 D_5cc20 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_5cc38 D_5cc38 (Z_to_bv 64 0xe2264).
    stepLD8 F_5cc3c D_5cc3c (Z_to_bv 64 0xf5d48).
    stepn F_5cc40 D_5cc40. sp_renorm.
    stepretL F_5cc44 D_5cc44 (0xe2264 : word).
    (* [comment removed for export] *)
    stepn F_e221c D_e221c.
    stepb_ft F_e2220 D_e2220 ltac:(cond_compute).
    stepLD8 F_e2224 D_e2224 (Z_to_bv 64 0xe22e8).
    stepLD8 F_e2228 D_e2228 code.
    stepLD8 F_e222c D_e222c s1v.
    stepn F_e2230 D_e2230. sp_renorm.
    (* [comment removed for export] *)
    stepn F_e2234 D_e2234.
    stepretL F_e21e8 D_e21e8 (0xe22e8 : word).
    stepn F_e22a0 D_e22a0.
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
    msteps RSEGS (mkst regs (0xe2280 : word) mem rom) (mkst regs' (0xe5fc0 : word) mem' rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0xe22ec
    /\ store_ok RSEGS mem' (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true
    /\ (forall (a : Z) n bs, rdn RSEGS mem (Z_to_bv 64 a) n = Some bs ->
          (0 <= a)%Z -> (a + Z.of_nat n <= 0x12c000)%Z ->
          (a + Z.of_nat n <= 0xfa598 \/ 0xfa599 <= a)%Z ->
          (a + Z.of_nat n <= 0x12a8a0 \/ 0x12a8b8 <= a)%Z ->
          (a + Z.of_nat n <= 0x12aac0 \/ 0x12aac4 <= a)%Z ->
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
  file_clean mem 0xfa438 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0xe2280 : word) mem (seg_rom RSEGS)) model)
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
  assert (FC1 : file_clean mem1 0xfa438 wp1 rp1).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (FC2 : file_clean mem1 0xfa348 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_clean fx v9_reloc v9_code v9_sites v9_data v9_rw
             regs1 mem1 model sp code wp1 rp1 wp2 rp2 Rsp Rs0 Rra Esplo Esphi SOK1 G1 FC1 FC2 Hh Hlazy).
Qed.
End VP1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stdout_pending_G : forall mem wb wp bufp bufsz rp1 can pending,
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  @StdioDefs.stdout_pending v9_reloc mem wb wp bufp bufsz rp1 can pending.
Proof.
  intros mem wb wp bufp bufsz rp1 can pending [f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14].
  exact (@StdioDefs.Build_stdout_pending v9_reloc mem wb wp bufp bufsz rp1 can pending
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
  realizes RSEGS (mkCfg (mkst regs (0xe2280 : word) mem (seg_rom RSEGS)) model)
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
  assert (FC2 : file_clean mem1 0xfa348 wp2 rp2).
  { repeat split; zaddr_goal; (apply TR; [assumption | cbn; lia ..]). }
  assert (SP1 : stdout_pending mem1 wb wp bufp bufsz rp1 can pending).
  { constructor; zaddr_goal; try assumption.
    1-9: (apply TR; [assumption | cbn; lia ..]).
    - apply TR; [assumption | lia ..].
    - split; (apply TR; [assumption | cbn; lia ..]). }
  rl_tail (@Exit.exit_tail_flush fx v9_reloc v9_code v9_sites v9_data v9_rw
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
  realizes RSEGS (mkCfg (mkst regs (0xe2280 : word) mem (seg_rom RSEGS)) model)
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
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0xe2280) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending PRE.
  replace (Z_to_bv 64 0xe2280) with (0xe2280 : word) by (apply bv_eq; reflexivity).
  exact (ref_exit regs mem model code pending PRE).
Qed.
End VP5.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End V9Exit.
