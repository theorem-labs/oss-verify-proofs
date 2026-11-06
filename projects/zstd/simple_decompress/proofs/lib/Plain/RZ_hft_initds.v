(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_hft_iface RZ_hft_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Theorem fse_initds_proof : fse_initds_stmt.
Proof.
  unfold fse_initds_stmt, PFSE_INITDS. intros until junk.
  intros MI STC BDC (BCR & BOK) BC2 SRCB SRCL DTB TLR R1 R2 R3 R4 R5 R6 R7 R8 D1 D2 D3 D4 D5.
  unfold bitd_cells in BDC.
  assert (MU : munch [(ST, ST + 16); (BD, BD + 40)] m m) by apply munch_refl.
  assert (WM : wmono psegs m m) by apply wmono_refl.
  apply (rw_cells_split_CB psegs _ _ [] 16 _ [] [8; 8]%nat) in STC; [| reflexivity]. cbn [mk_CB_cells app] in STC.
  lazymatch type of STC with rw_cells _ _ _ (CB 8 ?j :: ?post) => destruct (cb8_as_c8 psegs _ _ [] j post STC) as [w0 STC1] end. cbn [app] in STC1. clear STC.
  lazymatch type of STC1 with rw_cells _ _ _ (?c0 :: CB 8 ?j :: ?post) => destruct (cb8_as_c8 psegs _ _ [c0] j post STC1) as [w1 STC] end. cbn [app] in STC. clear STC1.
  lazymatch goal with |- _ => let a := cur_mem_addr in
    assert (RD : ov_read_bytes psegs m a 2 = Some (le2 (Z_to_bv 64 tl))) end.
  { pose proof (bytes_at_read psegs m DT (le2 (Z_to_bv 64 tl)) 0 2 DTB ltac:(lia) ltac:(rewrite length_le2; lia)) as X.
    replace (wa (DT + 0)) with (Z_to_bv 64 DT) in X by (unfold wa; f_equal; lia). exact X. }
  zstep.
  rewrite (zx16_u tl) by lia.
  zstep. rewrite (sx32w_small bc) by lia.
  zstep. zstep. zstep. zstep. rewrite (swrap32_small (bc + tl)) by lia.
  zstep. zstep.
  lazymatch goal with |- _ => let a := cur_mem_addr in
    pose proof (fbitmask_rd m tl a MI ltac:(lia) ltac:(unfold wa, FBITMASK; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RDM end.
  zstep.
  assert (P2 : 1 <= 2^tl <= 4096) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
  rewrite (zx32w_small (2^tl - 1)) by lia.
  zstep. zstep. zstep. zstep.
  lazymatch goal with |- _ => let v := reg_val 14 in lazymatch v with Z_to_bv 64 ?e => set (st := e) end end.
  assert (STR : 0 <= st < 2^tl) by (apply fland_mask_lt; lia). clearbody st.
  zstep. zstep. zstep. if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done. unfold fse_initds_post.
    do 15 eexists. eexists. exists st, cont, (bc + tl), 70616.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [exact STC|]. split; [exact STR|]. split; [exact BDC|]. split; [unfold fbit_ok; split; [lia| intros; lia]| lia].
  - specialize (BOK ltac:(lia)).
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    + (* [comment removed for export] *)
      zstep.
      rewrite (srliw_val (bc + tl) 3) by lia. rewrite (Z.mod_small (bc + tl) 4294967296) by lia. change (2^3) with 8.
      assert (QR : 0 <= (bc + tl) / 8 <= 8) by (clear - BCR TLR K; Z.div_mod_to_equations; lia).
      set (q := (bc + tl) / 8) in *.
      zstep.
      assert (PR : SRC <= ptr - q /\ ptr - q + 8 <= SRC + n) by (clear - BOK K2 QR; lia).
      lbyte SRCB. lbyte SRCB. lbyte SRCB. lbyte SRCB.
      do 4 zstep. lbyte SRCB. lbyte SRCB. zstep. lbyte SRCB. lbyte SRCB. do 8 zstep.
      zstep. zstep. forget_reg 15.
      replace (Z.land (bc + tl) 7) with ((bc + tl) mod 8) by (symmetry; apply land_7).
      zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done. unfold fse_initds_post.
      do 15 eexists. eexists. exists st, w, ((bc + tl) mod 8), (ptr - q).
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
      split; [exact STC|]. split; [exact STR|]. split; [exact BDC|].
      split; [unfold fbit_ok; split; [clear - BCR TLR; Z.div_mod_to_equations; lia| intros _; right; clear - PR BOK K2; lia]|].
      clear - BCR TLR; Z.div_mod_to_equations; lia.
    + zstep. zstep. if_cases K3; zify_cond K3.
      * (* [comment removed for export] *)
        zstep. zstep. zstep. apply evt_done. unfold fse_initds_post.
        do 15 eexists. eexists. exists st, cont, (bc + tl), ptr.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
        split; [exact STC|]. split; [exact STR|]. split; [exact BDC|].
        split; [unfold fbit_ok; split; [lia| intros _; left; lia]| lia].
      * (* [comment removed for export] *)
        zstep.
        rewrite (srliw_val (bc + tl) 3) by lia. rewrite (Z.mod_small (bc + tl) 4294967296) by lia. change (2^3) with 8.
        assert (QR : 0 <= (bc + tl) / 8 <= 8) by (clear - BCR TLR K; Z.div_mod_to_equations; lia).
        set (q := (bc + tl) / 8) in *.
        zstep. zstep. if_cases K4; zify_cond K4.
        -- zstep. zstep. zstep.
           rewrite (Z.mod_small q 4294967296) by lia.
           replace (q ≪ 3) with (8 * q) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
           zstep.
           assert (PR : SRC <= ptr - q /\ ptr - q + 8 <= SRC + n) by (clear - BOK K2 K3 K4 QR; lia).
           lbyte SRCB. lbyte SRCB. lbyte SRCB. lbyte SRCB.
           zstep.
           rewrite (swrap32_small (bc + tl - 8 * q)) by (clear - BCR TLR QR K; subst q; Z.div_mod_to_equations; lia).
           do 4 zstep. lbyte SRCB. lbyte SRCB. zstep. lbyte SRCB. lbyte SRCB. do 8 zstep.
           zstep. zstep. forget_reg 15.
           zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done. unfold fse_initds_post.
           do 15 eexists. eexists. exists st, w, (bc + tl - 8 * q), (ptr - q).
           split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
           split; [exact STC|]. split; [exact STR|]. split; [exact BDC|].
           split; [unfold fbit_ok; split; [clear - BCR TLR QR K; subst q; Z.div_mod_to_equations; lia| intros _; right; clear - PR BOK K2 K3; lia]|].
           clear - BCR TLR QR; lia.
        -- (* [comment removed for export] *)
           zstep. zstep. zstep. zstep.
           assert (DR : 1 <= ptr - SRC <= 7 /\ ptr - SRC < q /\ 8 <= n) by (clear - BOK K2 K3 K4 QR; lia).
           rewrite (Z.mod_small (ptr - SRC) 4294967296) by lia.
           replace ((ptr - SRC) ≪ 3) with (8 * (ptr - SRC)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
           zstep. replace (ptr - (ptr - SRC)) with SRC by lia.
           lbyte SRCB. lbyte SRCB. lbyte SRCB. lbyte SRCB.
           zstep.
           rewrite (swrap32_small (bc + tl - 8 * (ptr - SRC))) by (clear - BCR TLR QR K DR; subst q; Z.div_mod_to_equations; lia).
           do 4 zstep. lbyte SRCB. lbyte SRCB. zstep. lbyte SRCB. lbyte SRCB. do 8 zstep.
           zstep. zstep. forget_reg 15.
           zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done. unfold fse_initds_post.
           do 15 eexists. eexists. exists st, w, (bc + tl - 8 * (ptr - SRC)), SRC.
           split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
           split; [exact STC|]. split; [exact STR|]. split; [exact BDC|].
           split; [unfold fbit_ok; split; [clear - BCR TLR QR K DR; subst q; Z.div_mod_to_equations; lia| intros _; left; reflexivity]|].
           clear - BCR TLR QR DR; lia.
Qed.
