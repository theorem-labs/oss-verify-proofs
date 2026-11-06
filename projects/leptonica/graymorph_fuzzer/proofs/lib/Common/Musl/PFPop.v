(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import SumWalkTac Frame.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require Import RelocKit RCode_18000_19000 RImg.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require Import MuslTac MemcpyBase.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import PFLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require Import RelocKit .
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require Import MuslTac PFBase PFCore.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation W8 v := (word_to_le_bytes 8 (Z_to_bv 64 v)).
Abbreviation W4 v := (word_to_le_bytes 4 (Z_to_bv 64 v)).
Abbreviation X8 w := (word_to_le_bytes 8 w).

(* [comment removed for export] *)
Section VP1.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
Lemma firstn4_X8 : forall w : word, firstn 4 (word_to_le_bytes 8 w) = word_to_le_bytes 4 w.
Proof. intros w. reflexivity. Qed.

Lemma bytes_le_to_Z_X4 : forall w : word,
  bytes_le_to_Z (word_to_le_bytes 4 w) = bv_unsigned (Z_to_bv 64 (bv_unsigned w mod 2 ^ 32)).
Proof.
  intros w. rewrite bytes_le_N. change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z.
  pose proof (u64_range w). pose proof (Z.mod_pos_bound (bv_unsigned w) (2 ^ 32) ltac:(lia)).
  rewrite u_Z2bv; [reflexivity| |]; cbn in *; lia.
Qed.
End VP1.

Section POP.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
  Variables (sp0 : Z) (mem0 : word -> option byte) (cv : Z) (rom : word -> option byte).
  Hypothesis CTX : ctxH sp0 mem0 cv.
  Let Hcsp : (IMG_TOP + FR <= sp0 <= 0x800000000000)%Z := Csp _ _ _ CTX.

  Ltac sok := soks CTX.
  (* [comment removed for export] *)
  Ltac img_rd F C :=
    rl_addfold; rl_norm_s; rewrite ?v_addi_0; rl_addfold;
    lazymatch goal with
    | |- rdn _ _ (rl ?d ?c) ?n = _ =>
        change (rl d c) with (Z_to_bv 64 (c + d));
        rewrite (FRM_img _ _ _ CTX _ _ _ F); [exact C | lay; lia | lay; cbn; lia]
    end.

  Variables (m : word -> option byte) (k : Z) (w : word) (ty : Z).
  Hypothesis F : FRM sp0 mem0 m.
  Hypothesis Hap2 : rdn SEGS m (Z_to_bv 64 (sp0 - 2768)) 8 = Some (W8 (sp0 - 56 + 8 * k)).
  Hypothesis Hslot : VAslot m sp0 k w.
  Hypothesis Hk : (0 <= k < 7)%Z.

  (* [comment removed for export] *)
  Definition popM (v : word) : word -> option byte :=
    wbytes (wbytes m (Z_to_bv 64 (sp0 - 2768)) (W8 (sp0 - 56 + 8 * (k + 1)))) (Z_to_bv 64 (sp0 - 3200)) (X8 v).

  Lemma slot4 : rdn SEGS m (Z_to_bv 64 (sp0 - 56 + 8 * k)) 4 = Some (word_to_le_bytes 4 w).
  Proof. rewrite <- firstn4_X8. eapply rdn_firstn; [exact Hslot | lia]. Qed.

  (* [comment removed for export] *)
  Ltac pop_head C TBL FT :=
      stepn constr:(F_18d9c) constr:(D_18d9c); rwH;                                                                 (* [comment removed for export] *)
      stepn constr:(F_18da0) constr:(D_18da0);                                                                      (* [comment removed for export] *)
      stepb_ft constr:(F_18da4) constr:(D_18da4) ltac:(cond_vm);                                   (* [comment removed for export] *)
      stepn constr:(F_18da8) constr:(D_18da8);                                                                      (* [comment removed for export] *)
      stepn constr:(F_18dac) constr:(D_18dac);                                                                      (* [comment removed for export] *)
      stepn constr:(F_18db0) constr:(D_18db0);                                                                      (* [comment removed for export] *)
      stepn constr:(F_18db4) constr:(D_18db4);                                                                      (* [comment removed for export] *)
      stepLD constr:(F_18db8) constr:(D_18db8) (W4 TBL) (Z_to_bv 64 TBL) ltac:(img_rd F C) ltac:(apply bytes_le_to_Z_4; u_norm; lia);  (* [comment removed for export] *)
      rewrite (v_lw_small TBL) by lia;
      stepn constr:(F_18dbc) constr:(D_18dbc);                                                                      (* [comment removed for export] *)
      rewrite rl_rel_add;
      stepretK constr:(F_18dc0) constr:(D_18dc0) FT ltac:(rwH; reflexivity).                                       (* [comment removed for export] *)

  Theorem pop_arg_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = Z_to_bv 64 (sp0 - 3200) -> getr regs 11 = Z_to_bv 64 ty -> getr regs 12 = Z_to_bv 64 (sp0 - 2768) ->
    (ty = 9 \/ ty = 10 \/ ty = 11 \/ ty = 20)%Z ->
    exists r (v : word),
      msteps SEGS (mkst regs (rl dF_18d9c 0x18d9c) m rom) (mkst r ret (popM v) rom)
      /\ ((ty = 9 \/ ty = 20)%Z -> v = w)
      /\ (forall x : reg, x <> 11 -> x <> 13 -> getr r x = getr regs x).
  Proof.
    intros regs ret Hret H1 H10 H11 H12 Hty. pose proof Hcsp as Hsp0. lay.
    pose proof Hslot as SL. unfold VAslot in SL. pose proof slot4 as SL4. pose proof (u64_range w) as Hw.
    pose proof (Z.mod_pos_bound (bv_unsigned w) (2 ^ 32) ltac:(lia)) as Hm32.
    destruct Hty as [E | [E | [E | E]]]; rewrite E in H11.
    - (* [comment removed for export] *)
      eexists. exists w. split; [|split; [intros _; reflexivity|]].
      + pop_head img_115a8_4 ((0x18dc4 + dF_18d9c) - (0x115a8 + dA_114a8))%Z F_18dc4.
        stepLD8 F_18dc4 D_18dc4 (Z_to_bv 64 (sp0 - 56 + 8 * k)).                                 (* [comment removed for export] *)
        stepiv F_18dc8 D_18dc8 (Z_to_bv 64 (sp0 - 56 + 8 * (k + 1))) ltac:(zval).               (* [comment removed for export] *)
        stepST F_18dcc D_18dcc (Z_to_bv 64 (sp0 - 2768)) (Z_to_bv 64 (sp0 - 56 + 8 * (k + 1))) ltac:(sok).  (* [comment removed for export] *)
        stepLD8 F_18dd0 D_18dd0 w.                                                                (* [comment removed for export] *)
        stepST F_18dd4 D_18dd4 (Z_to_bv 64 (sp0 - 3200)) w ltac:(sok).                           (* [comment removed for export] *)
        stepret F_18dd8 D_18dd8 ret ltac:(exact H1).
        unfold popM. apply mst_refl.
      + intros x N11 N13. repeat (rewrite getr_other by assumption). reflexivity.
    - (* [comment removed for export] *)
      eexists. exists (v_lw (Z_to_bv 64 (bv_unsigned w mod 2 ^ 32))). split; [|split; [intros [?|?]; lia|]].
      + pop_head img_115ac_4 ((0x18eb8 + dF_18d9c) - (0x115a8 + dA_114a8))%Z F_18eb8.
        stepLD8 F_18eb8 D_18eb8 (Z_to_bv 64 (sp0 - 56 + 8 * k)).                                 (* [comment removed for export] *)
        stepiv F_18ebc D_18ebc (Z_to_bv 64 (sp0 - 56 + 8 * (k + 1))) ltac:(zval).               (* [comment removed for export] *)
        stepST F_18ec0 D_18ec0 (Z_to_bv 64 (sp0 - 2768)) (Z_to_bv 64 (sp0 - 56 + 8 * (k + 1))) ltac:(sok).  (* [comment removed for export] *)
        stepLD F_18ec4 D_18ec4 (word_to_le_bytes 4 w) (Z_to_bv 64 (bv_unsigned w mod 2 ^ 32))
          ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_X4).                             (* [comment removed for export] *)
        stepST F_18ec8 D_18ec8 (Z_to_bv 64 (sp0 - 3200)) (v_lw (Z_to_bv 64 (bv_unsigned w mod 2 ^ 32))) ltac:(sok).  (* [comment removed for export] *)
        stepret F_18ecc D_18ecc ret ltac:(exact H1).
        unfold popM. apply mst_refl.
      + intros x N11 N13. repeat (rewrite getr_other by assumption). reflexivity.
    - (* [comment removed for export] *)
      eexists. exists (Z_to_bv 64 (bv_unsigned w mod 2 ^ 32)). split; [|split; [intros [?|?]; lia|]].
      + pop_head img_115b0_4 ((0x18e30 + dF_18d9c) - (0x115a8 + dA_114a8))%Z F_18e30.
        stepLD8 F_18e30 D_18e30 (Z_to_bv 64 (sp0 - 56 + 8 * k)).                                 (* [comment removed for export] *)
        stepiv F_18e34 D_18e34 (Z_to_bv 64 (sp0 - 56 + 8 * (k + 1))) ltac:(zval).               (* [comment removed for export] *)
        stepST F_18e38 D_18e38 (Z_to_bv 64 (sp0 - 2768)) (Z_to_bv 64 (sp0 - 56 + 8 * (k + 1))) ltac:(sok).  (* [comment removed for export] *)
        stepLD F_18e3c D_18e3c (word_to_le_bytes 4 w) (Z_to_bv 64 (bv_unsigned w mod 2 ^ 32))
          ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_X4).                             (* [comment removed for export] *)
        stepST F_18e40 D_18e40 (Z_to_bv 64 (sp0 - 3200)) (Z_to_bv 64 (bv_unsigned w mod 2 ^ 32)) ltac:(sok).  (* [comment removed for export] *)
        stepret F_18e44 D_18e44 ret ltac:(exact H1).
        unfold popM. apply mst_refl.
      + intros x N11 N13. repeat (rewrite getr_other by assumption). reflexivity.
    - (* [comment removed for export] *)
      eexists. exists w. split; [|split; [intros _; reflexivity|]].
      + pop_head img_115d4_4 ((0x18dc4 + dF_18d9c) - (0x115a8 + dA_114a8))%Z F_18dc4.
        stepLD8 F_18dc4 D_18dc4 (Z_to_bv 64 (sp0 - 56 + 8 * k)).
        stepiv F_18dc8 D_18dc8 (Z_to_bv 64 (sp0 - 56 + 8 * (k + 1))) ltac:(zval).
        stepST F_18dcc D_18dcc (Z_to_bv 64 (sp0 - 2768)) (Z_to_bv 64 (sp0 - 56 + 8 * (k + 1))) ltac:(sok).
        stepLD8 F_18dd0 D_18dd0 w.
        stepST F_18dd4 D_18dd4 (Z_to_bv 64 (sp0 - 3200)) w ltac:(sok).
        stepret F_18dd8 D_18dd8 ret ltac:(exact H1).
        unfold popM. apply mst_refl.
      + intros x N11 N13. repeat (rewrite getr_other by assumption). reflexivity.
  Qed.
End POP.
