(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdFrameW ZdWalkKit ZdDctxRep.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_frame_iface RZ_block_iface RZ_dframe_iface.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section DECODEFH.
  Hypothesis GETFH : zd_getfh_stmt.
  Hypothesis XXHRESET : zd_xxh_reset_stmt.
  Variables (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SP DCTX SRC : Z) (src : list Z) (off hsz : Z)
            (fp : list cell) (pcs dsz bt stg le fe : word) (xs : list cell) (ws : list word) (lo : Z).
  Hypothesis FPC : dctx_fp psegs m DCTX fp.
  Hypothesis H3C : dctx_h3 psegs m DCTX pcs dsz bt stg le fe.
  Hypothesis XSC : dctx_xs psegs m DCTX xs.
  Hypothesis H5C : dctx_h5 psegs m DCTX ws.
  Hypothesis H5OK : h5_frame_ok ws.
  Hypothesis RD0 : 4096 <= DCTX.  Hypothesis RD1 : DCTX + 95992 < 2^47.
  Hypothesis SB : bytes_at psegs m SRC (map (Z_to_bv 8) src).
  Hypothesis OK : all_bytes src.
  Hypothesis OFF0 : 0 <= off.  Hypothesis N5 : 5 <= hsz.  Hypothesis OFS : off + hsz <= zlen src.  Hypothesis SRC0 : 0 < SRC.
  Hypothesis ST : stk psegs m lo SP.
  Hypothesis LO : lo <= SP - 128.
  Hypothesis RSP : 0 <= SP < 2^64.
  Hypothesis DS : DCTX + 95992 <= lo \/ SP <= DCTX.
  Hypothesis SS : SRC + zlen src <= lo \/ SP <= SRC.
  Hypothesis SD : SRC + zlen src <= DCTX \/ DCTX + 95992 <= SRC.
  Hypothesis MI : mem_inv psegs m.

  Notation W := [(DCTX + 29928, DCTX + 29984); (DCTX + 30008, DCTX + 30116); (SP - 128, SP)].
  Notation POST := (zd_decodefh_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP DCTX src off hsz pcs dsz bt stg le fe xs ws lo m).

  Lemma decodefh_body : evt psegs POST
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DCTX) (Z_to_bv 64 (SRC + off)) (Z_to_bv 64 hsz) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_DECODEFH) fc None m (seg_rom psegs)).
  Proof.
    unfold PZD_DECODEFH.
    destruct FPC as [FPC' FPSZ]. destruct XSC as [XSC' XSSZ]. destruct H5C as [H5C' H5L]. unfold dctx_h3 in H3C.
    destruct H5OK as (K_FMT & K_FIC & K_RMD & K_REST).
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl psegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ SB) as DB. rewrite length_map in DB.
    assert (LENP : zlen (map (Z_to_bv 8) src) = zlen src) by (rewrite length_map; reflexivity).
    pose proof ST as (LO0 & _ & _).
    h5_open ws H5L.
    unfold wz0 in *. subst b0 b1 b20.
    carve_frame 80%nat ST.
    do 9 zs. do 7 zs.
    rewrite sx32w_small by lia.
    zs. zs. zs.
    unfold PZD_GETFH in GETFH.
    call (GETFH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SP + -80) (DCTX + 29928) SRC src off hsz _ lo); [ exact SB | exact OK | exact OFF0 | exact N5 | exact OFS | exact SRC0 | exact FPC' | exact FPSZ | exact ST | lia | lia | lia | lia | lia | exact MI | reflexivity | reflexivity | reflexivity | reflexivity | ].
    rename PC into ST2. rename PC0 into FPC2. rename PC1 into FPSZ2. rename POST into ZFP. rename MI0 into MI2.
    set (gfh := get_frame_header src off hsz) in *.
    assert (RRET : 0 <= fh_retval gfh < 18446744073709551616).
    { destruct gfh as [hh|v] eqn:G; cbn [fh_retval]; [lia|]. pose proof (gfh_ret_pos src off hsz v N5 G). lia. }
    lazymatch goal with |- evt _ ?Q _ => set (Q0 := Q) end.
    assert (EPI : forall mm r fp' pcs' xs' ws' (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (z8 z9 z18 z19 z20 z21 z22 z23 : word),
      rw_cells psegs mm (SP + -80) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 (firstn 64 (firstn 72 junk))))))))); C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      stk psegs mm lo (SP + -80) -> munch W m mm -> wmono psegs m mm -> mem_inv psegs mm ->
      dctx_fp psegs mm DCTX fp' -> dctx_h3 psegs mm DCTX pcs' dsz bt stg le fe -> dctx_xs psegs mm DCTX xs' -> dctx_h5 psegs mm DCTX ws' ->
      Z_to_bv 64 r = Z_to_bv 64 (decode_frame_header src off hsz) ->
      match gfh with
      | FH_ok h => fp' = zfh_cells h /\ pcs' = Z_to_bv 64 (bv_unsigned pcs + hsz)
                   /\ ws' = wupd [b; Z_to_bv 64 0; Z_to_bv 64 0; b2; b3; b4; b5; b6; b7; b8; b9; b10; b11; b12; b13; b14; b15; b16; b17; b18; b19; Z_to_bv 64 0; b21; b22; b23; b24; b25; b26; b27; b28; b29; b30; b31; b32; b33; b34; b35; b36; b37; b38; b39; b40; b41; b42] H5_validateChecksum (Z_to_bv 64 (if fh_checksum h =? 0 then 0 else 1))
                   /\ (if fh_checksum h =? 0 then xs' = xs else exists j1 j2, xs' = xxh_cells j1 0 j2)
      | FH_ret _ => pcs' = pcs /\ xs' = xs /\ ws' = [b; Z_to_bv 64 0; Z_to_bv 64 0; b2; b3; b4; b5; b6; b7; b8; b9; b10; b11; b12; b13; b14; b15; b16; b17; b18; b19; Z_to_bv 64 0; b21; b22; b23; b24; b25; b26; b27; b28; b29; b30; b31; b32; b33; b34; b35; b36; b37; b38; b39; b40; b41; b42]
      end ->
      evt psegs Q0
        (MS (mkR y1 (Z_to_bv 64 (SP + -80)) gp tp y5 y6 y7 z8 z9 (Z_to_bv 64 r) y11 y12 y13 y14 y15 y16 y17 z18 z19 z20 z21 z22 z23 s8 s9 s10 s11 y28 y29 y30 y31)
            F (Z_to_bv 64 0x15b68) fc None mm (seg_rom psegs))).
    { intros mm r fp' pcs' xs' ws' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 z8 z9 z18 z19 z20 z21 z22 z23 FRm STm MUm WMm MIm A1 A2 A3 A4 ER CASES.
      do 10 zs. release_frame FRm STm SP. zs. rewrite ER.
      apply evt_done. unfold Q0, zd_decodefh_post. fold gfh. do 14 eexists. exists mm, fp', pcs', xs', ws'.
      split; [reflexivity|]. split; [exact MUm|]. split; [exact WMm|]. split; [exact MIm|]. split; [exact STm|].
      split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. exact CASES. }

    zs. zs. if_cases KE; zify_cond KE.
    - (* [comment removed for export] *)
      match type of H5OK with h5_frame_ok ?l => set (WS := l) in * end.
      destruct gfh as [hh|v] eqn:G; cbn [fh_retval] in *; [exfalso; lia|].
      eapply (EPI _ v _ _ _ WS); try eassumption.
      + split; [exact FPC2| exact FPSZ2].
      + split; [exact XSC'| exact XSSZ].
      + split; [exact H5C'| reflexivity].
      + unfold decode_frame_header. fold gfh. rewrite G.
        replace (zd_is_error v) with true by (symmetry; apply zd_is_error_true_iff; change (2^64) with 18446744073709551616; lia). reflexivity.
      + repeat split.
    - match type of H5OK with h5_frame_ok ?l => set (WS := l) in * end.
      zs. if_cases K0; zify_cond K0.
      + (* [comment removed for export] *)
        destruct gfh as [h|v] eqn:G; cbn [fh_retval] in *; [| exfalso; pose proof (gfh_ret_pos src off hsz v N5 G); lia].
        rewrite (ZFP h eq_refl) in FPC2. clear ZFP.
        pose proof (get_frame_header_ok src OK off hsz h G) as (_ & _ & _ & _ & _ & _ & _ & RCK & _).
        assert (DFH : decode_frame_header src off hsz = 0) by (unfold decode_frame_header; fold gfh; rewrite G; reflexivity).
        unfold zfh_cells in FPC2.
        zs. rewrite sx32w_small by lia. zs. zs. if_cases KR; zify_cond KR; [| exfalso; lia].
        zs. rewrite sx32w_small by lia.
        assert (TAIL : forall mm xs' (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (z19 z20 z21 z22 z23 : word),
          rw_cells psegs mm (SP + -80) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 (firstn 64 (firstn 72 junk))))))))); C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
          stk psegs mm lo (SP + -80) -> munch W m mm -> wmono psegs m mm -> mem_inv psegs mm ->
          rw_cells psegs mm (DCTX + 29928) (zfh_cells h) ->
          rw_cells psegs mm (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 fe] ->
          rw_cells psegs mm (DCTX + 30008) xs' -> cells_size xs' = 88%nat ->
          rw_cells psegs mm (DCTX + 30096) (h5_cells (wupd WS H5_validateChecksum (Z_to_bv 64 (if fh_checksum h =? 0 then 0 else 1)))) ->
          (if fh_checksum h =? 0 then xs' = xs else exists j1 j2, xs' = xxh_cells j1 0 j2) ->
          evt psegs Q0
            (MS (mkR y1 (Z_to_bv 64 (SP + -80)) gp tp y5 y6 y7 (Z_to_bv 64 hsz) (Z_to_bv 64 DCTX) y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (DCTX + 29956)) z19 z20 z21 z22 z23 s8 s9 s10 s11 y28 y29 y30 y31)
                F (Z_to_bv 64 0x15b58) fc None mm (seg_rom psegs))).
        { intros mm xs' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 z19 z20 z21 z22 z23 FRm STm MUm WMm MIm A1 A2 A3 A3S A4 A5.
          unfold zfh_cells in A1. unfold WS in A4. cbv beta iota delta [h5_cells h5_sizes mk_wcells wupd H5_validateChecksum] in A4.
          zs. zs. zs. zs.
          eapply (EPI _ 0 (zfh_cells h) _ xs' (wupd WS H5_validateChecksum (Z_to_bv 64 (if fh_checksum h =? 0 then 0 else 1)))); try eassumption.
          all: first [ exact A2 | (split; [exact A1| reflexivity]) | (split; [exact A3| exact A3S]) | (split; [exact A4| reflexivity])
                     | (rewrite DFH; reflexivity)
                     | (split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity| exact A5]) ]. }
        zs. if_cases KC; zify_cond KC.
        * (* [comment removed for export] *)
          zs.
          eapply (TAIL _ xs); try eassumption.
          -- rewrite KC. exact H5C'.
          -- rewrite KC. reflexivity.
        * (* [comment removed for export] *)
          zs. rewrite sx32w_small by lia. zs. zs. zs. if_cases KF; zify_cond KF; [exfalso; lia|].
          zs. zs. zs. zs. zs.
          unfold PZD_XXH_RESET in XXHRESET.
          call (XXHRESET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SP + -80) (DCTX + 30008) xs lo);
            [ exact XSC' | exact XSSZ | exact ST2 | lia | lia | lia | exact MI2 | reflexivity | ].
          destruct POST as (j1 & j2 & XS2).
          zs.
          eapply (TAIL _ (xxh_cells j1 0 j2)); try eassumption.
          -- reflexivity.
          -- replace (fh_checksum h =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
             match goal with H : rw_cells psegs _ (DCTX + 30096) _ |- _ => exact H end.
          -- replace (fh_checksum h =? 0) with false by (symmetry; apply Z.eqb_neq; lia). do 2 eexists. reflexivity.
      + (* [comment removed for export] *)
        destruct gfh as [hh|v] eqn:G; cbn [fh_retval] in *; [exfalso; lia|].
        zs. zs.
        eapply (EPI _ (-72) _ _ _ WS); try eassumption.
        all: first [ (split; [exact FPC2| exact FPSZ2]) | (split; [exact XSC'| exact XSSZ]) | (split; [exact H5C'| reflexivity])
                   | (repeat split) | idtac ].
        unfold decode_frame_header. fold gfh. rewrite G.
        replace (zd_is_error v) with false by (symmetry; apply zd_is_error_false_iff; change (2^64) with 18446744073709551616; lia).
        apply Z_to_bv_eqm. reflexivity.
  Qed.
End DECODEFH.

Theorem zd_decodefh_proof : zd_getfh_stmt -> zd_xxh_reset_stmt -> zd_decodefh_stmt.
Proof.
  intros GETFH XXHRESET. intros until lo. intros FPC H3C XSC H5C H5OK RD0 RD1 SB OK OFF0 N5 OFS SRC0 ST LO RSP DS SS SD MI -> -> ->.
  eapply decodefh_body; eassumption.
Qed.
Print Assumptions zd_decodefh_proof.
