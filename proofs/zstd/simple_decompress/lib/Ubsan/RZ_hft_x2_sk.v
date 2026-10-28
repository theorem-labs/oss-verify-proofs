(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdHufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWR ZdHufWX ZdHufWY.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_hft_iface RZ_hft_bdt_defs RZ_hft_x2_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section SK.
  Variables (gp tp x1 x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
            (SPF DT : Z) (m0 : fmem) (cw0 : list Z).
  Hypothesis DTL : 4096 <= DT.  Hypothesis DTH : DT + 16388 < 2^47.
  Variables (pos nb D : Z).
  Hypothesis POSR : 0 <= pos.  Hypothesis NBR : 0 <= nb <= 12.
  Hypothesis DR : 0 <= D < 18446744073709551616.
  Hypothesis W1 : hidden ((D ≫ 16) mod 2^16 = nb + 256).  Hypothesis W3 : hidden ((D ≫ 48) mod 2^16 = nb + 256).

  Notation ST pc mm x5 x6 x10 x11 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation POST n := (x2_sk_post gp tp x1 x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc SPF DT m0 cw0 pos n (nb + 256)).
  Ltac chk := zstep; let K := fresh "K" in if_cases K; zify_cond K; [exfalso; rewrite ?signed_lit in K by lia; lia | clear K].
  Ltac w1 := unfold hidden in W1; rewrite W1; rewrite Z.mod_small; [reflexivity | change (2^16) with 65536; lia].
  Ltac w3 := unfold hidden in W3; rewrite W3; rewrite Z.mod_small; [reflexivity | change (2^16) with 65536; lia].

  (* [comment removed for export] *)
  Lemma x2_sk_loop : forall j m cw q NQ sk x5 x6,
    Z.to_nat (NQ - q) = j -> 0 <= q < NQ -> 8 * (NQ - 1) < sk <= 8 * NQ -> pos + 8 * NQ <= 4096 ->
    mem_inv usegs m -> munch [(DT + 4, DT + 16388)] m0 m -> wmono usegs m0 m ->
    x2_cells m DT cw -> cells_written cw0 cw pos (8 * q) (nb + 256) -> x26 = Z_to_bv 64 (DT + 4 + 4 * pos) ->
    evt usegs (POST (8 * NQ))
      (ST 0x1f9ac m x5 x6 (Z_to_bv 64 (D ≫ 48)) (Z_to_bv 64 (D ≫ 32)) (Z_to_bv 64 (D ≫ 16)) (Z_to_bv 64 D) (Z_to_bv 64 sk)
          (Z_to_bv 64 (DT + 20 + 4 * (pos + 8 * q))) (Z_to_bv 64 (DT + 4 + 4 * (pos + 8 * q))) (Z_to_bv 64 (8 * q))).
  Proof.
    induction j as [|j IH]; intros until x6; intros EJ QR SKR PH MI MU WM (CW & CWL) CWR EX26; [exfalso; lia|].
    subst x26.
    remember (2 * (pos + 8 * q)) as b eqn:EB.
    chk. chk. zstep.
    u16st CW b D; [reflexivity|].
    u16st CW (b + 1) (nb + 256); [w1|].
    u16st CW (b + 2) (D ≫ 32); [reflexivity|].
    u16st CW (b + 3) (nb + 256); [w3|].
    zstep. chk.
    u16st CW (b + 4) D; [reflexivity|].
    u16st CW (b + 5) (nb + 256); [w1|].
    u16st CW (b + 6) (D ≫ 32); [reflexivity|].
    u16st CW (b + 7) (nb + 256); [w3|].
    zstep. chk.
    u16st CW (b + 8) D; [reflexivity|].
    u16st CW (b + 9) (nb + 256); [w1|].
    u16st CW (b + 10) (D ≫ 32); [reflexivity|].
    u16st CW (b + 11) (nb + 256); [w3|].
    zstep. chk.
    zstep. rewrite ?swrap32_small by lia.
    u16st CW (b + 12) D; [reflexivity|].
    u16st CW (b + 13) (nb + 256); [w1|].
    u16st CW (b + 14) (D ≫ 32); [reflexivity|].
    u16st CW (b + 15) (nb + 256); [w3|].
    chk. zstep. zstep. zstep.
    lazymatch type of CW with u8arr _ _ _ (u16s (map _ ?l)) => remember l as cw' eqn:ECW' end.
    assert (RND : cells_written cw cw' (pos + 8 * q) 8 (nb + 256)) by (subst cw' b; cw_round).
    pose proof (cells_written_app cw0 cw cw' pos (8 * q) 8 (nb + 256) POSR ltac:(lia) ltac:(lia) CWR RND) as CWR'.
    assert (CWL' : Z.of_nat (length cw') = 8192) by (subst cw'; rewrite !Zupd_length; exact CWL).
    clear ECW' RND.
    zstep. if_cases KB; zify_cond KB; rewrite ?signed_lit in KB by lia.
    - setreg 16 (Z_to_bv 64 (DT + 4 + 4 * (pos + 8 * (q + 1)))) ltac:(f_equal; lia).
      setreg 15 (Z_to_bv 64 (DT + 20 + 4 * (pos + 8 * (q + 1)))) ltac:(f_equal; lia).
      setreg 17 (Z_to_bv 64 (8 * (q + 1))) ltac:(f_equal; lia).
      replace (8 * q + 8) with (8 * (q + 1)) in CWR' by lia.
      eapply (IH m cw' (q + 1) NQ sk); try eassumption; try lia; try reflexivity. split; assumption.
    - apply evt_done. unfold x2_sk_post. do 10 eexists. exists m, cw'.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [split; assumption|].
      replace (8 * NQ) with (8 * q + 8) by lia. exact CWR'.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_sk_len2 : forall m cw x5 x6 x14 x15 x16 x17,
    pos + 2 <= 4096 -> mem_inv usegs m -> munch [(DT + 4, DT + 16388)] m0 m -> wmono usegs m0 m ->
    x2_cells m DT cw -> cw = cw0 -> x26 = Z_to_bv 64 (DT + 4 + 4 * pos) ->
    evt usegs (POST 2)
      (ST 0x1f97c m x5 x6 (Z_to_bv 64 (D ≫ 48)) (Z_to_bv 64 (D ≫ 32)) (Z_to_bv 64 (D ≫ 16)) (Z_to_bv 64 D) x14 x15 x16 x17).
  Proof.
    intros until x17; intros PH MI MU WM (CW & CWL) ECW EX26. subst cw x26.
    remember (2 * pos) as b eqn:EB.
    u16st CW b D; [reflexivity|].
    u16st CW (b + 1) (nb + 256); [w1|].
    u16st CW (b + 2) (D ≫ 32); [reflexivity|].
    u16st CW (b + 3) (nb + 256); [w3|].
    zstep.
    lazymatch type of CW with u8arr _ _ _ (u16s (map _ ?l)) => remember l as cw' eqn:ECW' end.
    assert (RND : cells_written cw0 cw' pos 2 (nb + 256)) by (subst cw' b; cw_round).
    assert (CWL' : Z.of_nat (length cw') = 8192) by (subst cw'; rewrite !Zupd_length; exact CWL).
    apply evt_done. unfold x2_sk_post. do 10 eexists. exists m, cw'.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [split; assumption | exact RND].
  Qed.

  (* [comment removed for export] *)
  Lemma x2_sk_len4 : forall m cw x5 x6 x14 x15 x16 x17,
    pos + 4 <= 4096 -> mem_inv usegs m -> munch [(DT + 4, DT + 16388)] m0 m -> wmono usegs m0 m ->
    x2_cells m DT cw -> cw = cw0 -> x26 = Z_to_bv 64 (DT + 4 + 4 * pos) ->
    evt usegs (POST 4)
      (ST 0x1f950 m x5 x6 (Z_to_bv 64 (D ≫ 48)) (Z_to_bv 64 (D ≫ 32)) (Z_to_bv 64 (D ≫ 16)) (Z_to_bv 64 D) x14 x15 x16 x17).
  Proof.
    intros until x17; intros PH MI MU WM (CW & CWL) ECW EX26. subst cw x26.
    remember (2 * pos) as b eqn:EB.
    u16st CW b D; [reflexivity|].
    u16st CW (b + 1) (nb + 256); [w1|].
    u16st CW (b + 2) (D ≫ 32); [reflexivity|].
    u16st CW (b + 3) (nb + 256); [w3|].
    zstep. chk.
    u16st CW (b + 4) D; [reflexivity|].
    u16st CW (b + 5) (nb + 256); [w1|].
    u16st CW (b + 6) (D ≫ 32); [reflexivity|].
    u16st CW (b + 7) (nb + 256); [w3|].
    zstep.
    lazymatch type of CW with u8arr _ _ _ (u16s (map _ ?l)) => remember l as cw' eqn:ECW' end.
    assert (RND : cells_written cw0 cw' pos 4 (nb + 256)) by (subst cw' b; cw_round).
    assert (CWL' : Z.of_nat (length cw') = 8192) by (subst cw'; rewrite !Zupd_length; exact CWL).
    apply evt_done. unfold x2_sk_post. do 10 eexists. exists m, cw'.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [split; assumption | exact RND].
  Qed.
End SK.
