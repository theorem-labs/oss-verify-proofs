(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdHufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWR ZdHufWX ZdHufWY.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_hft_iface RZ_hft_bdt_defs RZ_hft_x2_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section SK.
  Variables (gp tp x1 x5 x6 x7 x11 x13 x14 x15 x16 x18 x19 x20 x23 x24 x25 x26 x27 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
            (SPF DT : Z) (m0 : fmem) (cw0 : list Z).
  Hypothesis DTL : 4096 <= DT.  Hypothesis DTH : DT + 16388 < 2^47.
  Variables (pos nb D : Z).
  Hypothesis POSR : 0 <= pos.  Hypothesis NBR : 0 <= nb <= 12.
  Hypothesis DR : 0 <= D < 18446744073709551616.
  Hypothesis W1 : hidden ((D ≫ 16) mod 2^16 = nb + 256).  Hypothesis W3 : hidden ((D ≫ 48) mod 2^16 = nb + 256).

  Notation ST pc mm x8 x9 x10 x12 x17 x21 x22 x28 :=
    (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
  Notation POST n := (x2_sk_post gp tp x1 x5 x6 x7 x11 x13 x14 x15 x16 x18 x19 x20 x23 x24 x25 x26 x27 x29 x30 x31 F fc SPF DT m0 cw0 pos n (nb + 256)).
  Ltac w1 := unfold hidden in W1; rewrite W1; rewrite Z.mod_small; [reflexivity | change (2^16) with 65536; lia].
  Ltac w3 := unfold hidden in W3; rewrite W3; rewrite Z.mod_small; [reflexivity | change (2^16) with 65536; lia].

  (* [comment removed for export] *)
  Lemma x2_sk_loop : forall j m cw q NQ x10 x21,
    Z.to_nat (NQ - q) = j -> 0 <= q < NQ -> pos + 8 * NQ <= 4096 ->
    mem_inv psegs m -> munch [(DT + 4, DT + 16388)] m0 m -> wmono psegs m0 m ->
    x2_cells m DT cw -> cells_written cw0 cw pos (8 * q) (nb + 256) ->
    evt psegs (POST (8 * NQ))
      (ST 0x1d5b4 m (Z_to_bv 64 (DT + 20 + 4 * (pos + 8 * q))) (Z_to_bv 64 (DT + 20 + 4 * (pos + 8 * NQ))) x10 (Z_to_bv 64 D) (Z_to_bv 64 (D ≫ 48)) x21
          (Z_to_bv 64 (D ≫ 16)) (Z_to_bv 64 (D ≫ 32))).
  Proof.
    induction j as [|j IH]; intros until x21; intros EJ QR PH MI MU WM (CW & CWL) CWR; [exfalso; lia|].
    replace (Z_to_bv 64 (DT + 20 + 4 * (pos + 8 * q))) with (Z_to_bv 64 (DT + 4 + 2 * (2 * (pos + 8 * q)) + 16)) by (f_equal; lia).
    remember (2 * (pos + 8 * q)) as b eqn:EB.
    u16st CW b D; [reflexivity|].
    u16st CW (b + 1) (nb + 256); [w1|].
    u16st CW (b + 2) (D ≫ 32); [reflexivity|].
    u16st CW (b + 3) (nb + 256); [w3|].
    u16st CW (b + 4) D; [reflexivity|].
    u16st CW (b + 5) (nb + 256); [w1|].
    u16st CW (b + 6) (D ≫ 32); [reflexivity|].
    u16st CW (b + 7) (nb + 256); [w3|].
    u16st CW (b + 8) D; [reflexivity|].
    u16st CW (b + 9) (nb + 256); [w1|].
    u16st CW (b + 10) (D ≫ 32); [reflexivity|].
    u16st CW (b + 11) (nb + 256); [w3|].
    u16st CW (b + 12) D; [reflexivity|].
    u16st CW (b + 13) (nb + 256); [w1|].
    u16st CW (b + 14) (D ≫ 32); [reflexivity|].
    u16st CW (b + 15) (nb + 256); [w3|].
    zstep.
    lazymatch type of CW with u8arr _ _ _ (u16s (map _ ?l)) => remember l as cw' eqn:ECW' end.
    assert (RND : cells_written cw cw' (pos + 8 * q) 8 (nb + 256)) by (subst cw' b; cw_round).
    pose proof (cells_written_app cw0 cw cw' pos (8 * q) 8 (nb + 256) POSR ltac:(lia) ltac:(lia) CWR RND) as CWR'.
    assert (CWL' : Z.of_nat (length cw') = 8192) by (subst cw'; rewrite !Zupd_length; exact CWL).
    clear ECW' RND.
    zstep. if_cases KB; zify_cond KB.
    - lazymatch goal with |- _ => let v := reg_val 8 in replace v with (Z_to_bv 64 (DT + 20 + 4 * (pos + 8 * (q + 1)))) by (f_equal; lia) end.
      replace (8 * q + 8) with (8 * (q + 1)) in CWR' by lia.
      eapply (IH m cw' (q + 1) NQ); try eassumption; try lia. split; assumption.
    - apply evt_done. unfold x2_sk_post. do 8 eexists. exists m, cw'.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [split; assumption|].
      replace (8 * NQ) with (8 * q + 8) by lia. exact CWR'.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_sk_len2 : forall m cw x8 x9 x10 x21,
    pos + 2 <= 4096 -> mem_inv psegs m -> munch [(DT + 4, DT + 16388)] m0 m -> wmono psegs m0 m ->
    x2_cells m DT cw -> cw = cw0 -> x29 = Z_to_bv 64 (DT + 4 + 4 * pos) ->
    evt psegs (POST 2)
      (ST 0x1d574 m x8 x9 x10 (Z_to_bv 64 D) (Z_to_bv 64 (D ≫ 48)) x21 (Z_to_bv 64 (D ≫ 16)) (Z_to_bv 64 (D ≫ 32))).
  Proof.
    intros until x21; intros PH MI MU WM (CW & CWL) ECW EX29. subst cw x29.
    replace (Z_to_bv 64 (DT + 4 + 4 * pos)) with (Z_to_bv 64 (DT + 4 + 2 * (2 * pos) + 0)) by (f_equal; lia).
    remember (2 * pos) as b eqn:EB.
    u16st CW b D; [reflexivity|].
    u16st CW (b + 1) (nb + 256); [w1|].
    u16st CW (b + 2) (D ≫ 32); [reflexivity|].
    u16st CW (b + 3) (nb + 256); [w3|].
    zstep.
    lazymatch type of CW with u8arr _ _ _ (u16s (map _ ?l)) => remember l as cw' eqn:ECW' end.
    assert (RND : cells_written cw0 cw' pos 2 (nb + 256)) by (subst cw' b; cw_round).
    assert (CWL' : Z.of_nat (length cw') = 8192) by (subst cw'; rewrite !Zupd_length; exact CWL).
    apply evt_done. unfold x2_sk_post. do 8 eexists. exists m, cw'.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [split; assumption | exact RND].
  Qed.

  (* [comment removed for export] *)
  Lemma x2_sk_len4 : forall m cw x8 x9 x10 x21,
    pos + 4 <= 4096 -> mem_inv psegs m -> munch [(DT + 4, DT + 16388)] m0 m -> wmono psegs m0 m ->
    x2_cells m DT cw -> cw = cw0 -> x29 = Z_to_bv 64 (DT + 4 + 4 * pos) ->
    evt psegs (POST 4)
      (ST 0x1d550 m x8 x9 x10 (Z_to_bv 64 D) (Z_to_bv 64 (D ≫ 48)) x21 (Z_to_bv 64 (D ≫ 16)) (Z_to_bv 64 (D ≫ 32))).
  Proof.
    intros until x21; intros PH MI MU WM (CW & CWL) ECW EX29. subst cw x29.
    replace (Z_to_bv 64 (DT + 4 + 4 * pos)) with (Z_to_bv 64 (DT + 4 + 2 * (2 * pos) + 0)) by (f_equal; lia).
    remember (2 * pos) as b eqn:EB.
    u16st CW b D; [reflexivity|].
    u16st CW (b + 1) (nb + 256); [w1|].
    u16st CW (b + 2) (D ≫ 32); [reflexivity|].
    u16st CW (b + 3) (nb + 256); [w3|].
    u16st CW (b + 4) D; [reflexivity|].
    u16st CW (b + 5) (nb + 256); [w1|].
    u16st CW (b + 6) (D ≫ 32); [reflexivity|].
    u16st CW (b + 7) (nb + 256); [w3|].
    zstep.
    lazymatch type of CW with u8arr _ _ _ (u16s (map _ ?l)) => remember l as cw' eqn:ECW' end.
    assert (RND : cells_written cw0 cw' pos 4 (nb + 256)) by (subst cw' b; cw_round).
    assert (CWL' : Z.of_nat (length cw') = 8192) by (subst cw'; rewrite !Zupd_length; exact CWL).
    apply evt_done. unfold x2_sk_post. do 8 eexists. exists m, cw'.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [split; assumption | exact RND].
  Qed.
End SK.
