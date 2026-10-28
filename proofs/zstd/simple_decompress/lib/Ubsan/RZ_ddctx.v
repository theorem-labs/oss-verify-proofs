(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdFrameW ZdWalkKit ZdCellKit ZdDctxRep ZdSepKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_frame_iface RZ_block_iface RZ_dframe_iface RZ_dctx_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import frame_kit.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac transport_chunks segs m a bs ::= zd_transport_chunks segs m a bs.

Section DDCTX.
  Hypothesis DMF : zd_dmf_stmt.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SP lo DCTX DST CAP SRC : Z) (src : list Z) (size : Z).
  Hypothesis RD0 : 4096 <= DCTX.  Hypothesis RD1 : DCTX + 95992 < 2^47.  Hypothesis RD8 : DCTX mod 8 = 0.
  Hypothesis OK : all_bytes src.
  Hypothesis N0 : 0 <= size.  Hypothesis NLEN : size <= zlen src.  Hypothesis N40 : size < 2^40.
  Hypothesis RS0 : 4096 <= SRC.  Hypothesis RS1 : SRC + zlen src < 2^47.
  Hypothesis RC0 : 0 <= CAP.  Hypothesis RC40 : CAP < 2^40.
  Hypothesis DNULL : zimp (DST = 0) (CAP = 0).  Hypothesis DNN : zimp (DST <> 0) (4096 <= DST).  Hypothesis RDST : DST + CAP < 2^47.
  Hypothesis RLO : 4096 <= lo.  Hypothesis LO : lo <= SP - 2368.  Hypothesis RSP : SP < 2^47.  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis S_DC : zsep DCTX (DCTX + 95992) lo SP.
  Hypothesis S_DS : zsep DST (DST + CAP) lo SP.
  Hypothesis S_SR : zsep SRC (SRC + zlen src) lo SP.
  Hypothesis S_GT : zsep 0x36e40 (0x36e40 + 16) lo SP.
  Hypothesis D_DC : zsep DST (DST + CAP) DCTX (DCTX + 95992).
  Hypothesis D_SR : zsep DST (DST + CAP) SRC (SRC + zlen src).
  Hypothesis SR_DC : zsep SRC (SRC + zlen src) DCTX (DCTX + 95992).
  Hypothesis GT_DC : zsep 0x36e40 (0x36e40 + 16) DCTX (DCTX + 95992).
  Hypothesis GT_DS : zsep 0x36e40 (0x36e40 + 16) DST (DST + CAP).

  Notation W := [(DCTX, DCTX + 95992); (DST, DST + CAP); (SP - 2368, SP)].
  Notation POST := (zd_dmf_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP DCTX DST CAP src size lo m).

  Lemma ddctx_body : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word),
    dctx_any m DCTX -> rw_cells usegs m 0x36e40 [C8 wz0; C8 wz0] -> bytes_at usegs m SRC (map (Z_to_bv 8) src) ->
    stk usegs m DST (DST + CAP) -> stk usegs m lo SP -> mem_inv usegs m ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DCTX) (Z_to_bv 64 DST) (Z_to_bv 64 CAP) (Z_to_bv 64 SRC) (Z_to_bv 64 size)
               a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_DDCTX) fc None m (seg_rom usegs)).
  Proof.
    intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 DA GOT SB DSK ST MI.
    unfold PZD_DDCTX.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ SB) as DB. rewrite length_map in DB.
    assert (LENP : zlen (map (Z_to_bv 8) src) = zlen src) by (rewrite length_map; reflexivity).
    pose proof DSK as (DST0 & _ & _).
    assert (MU2 : munch [(SP + -64, SP)] m m) by apply munch_refl.
    assert (WM2 : wmono usegs m m) by apply wmono_refl.
    zs. fck. zs. zs. fck.
    carve_frame 64%nat ST.
    do 8 zs.
    lazymatch type of MU2 with munch _ _ ?mm =>
      assert (DA1 : dctx_any mm DCTX) by (eapply (dctx_any_transport DCTX [(SP + -64, SP)] m mm); [exact DA | exact MU2 | exact WM2 | dj_solve])
    end.
    clear DA MU2 WM2.
    destruct DA1 as (llt & mlt & oft & huf & pde & pfx & vst & dend & expd & fp & pcs & dsz & bt & stg & le & fe & xs & ws & jhb & ovd & dcb & dce & trace &
                    PT & H1 & [FPC FPSZ] & H3 & [XSC XSSZ] & [H5C H5L] & H5OK & TX & [OWE OWX]).
    unfold dctx_ptrs in PT. unfold dctx_h1 in H1. unfold dctx_h3 in H3. unfold dctx_tx in TX.
    pose proof H5OK as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K_DL & K_DD & K_DU & K9 & K10).
    h5_open ws H5L. unfold wz0 in K_DL, K_DD, K_DU. subst b13 b14 b17.
    zs. zs. zs.
    zs. rewrite sx32w_small by lia. zs. zs. if_false. zs. zs. if_true.
    zs. do 6 zs. zs. carve_frame 32%nat ST. do 5 zs. zs. if_true. do 7 zs. release_frame FR0 ST (SP + -64).
    do 6 zs.
    zs. zs. zs.
    zs. zs. do 7 zs.
    eapply stk_release in FR; [| exact ST | lia]. cbn [cells_size csize Nat.add] in FR.
    replace (SP + -64 + Z.of_nat 64) with SP in FR by lia. clear ST.
    zs. zs.
    assert (DA2 : dctx_any m1 DCTX).
    { eexists llt, mlt, oft, huf, pde, pfx, vst, dend, expd, fp, pcs, dsz, bt, stg, le, fe, xs,
              [b; b0; b1; b2; b3; b4; b5; b6; b7; b8; b9; b10; b11; b12; Z_to_bv 64 0; Z_to_bv 64 0; b15; b16; Z_to_bv 64 0; b18; b19; b20; b21; b22; b23; b24; b25;
               b26; b27; b28; b29; b30; b31; b32; b33; b34; b35; b36; b37; b38; b39; b40; b41; b42], jhb, ovd, dcb, dce, trace.
      split; [exact PT|]. split; [exact H1|]. split; [split; [exact FPC| exact FPSZ]|]. split; [exact H3|]. split; [split; [exact XSC| exact XSSZ]|].
      split; [split; [exact H5C| reflexivity]|]. split; [exact H5OK|]. split; [exact TX|]. split; [exact OWE| exact OWX]. }
    unfold PZD_DMF in DMF.
    eapply evt_mono.
    - eapply (DMF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SP lo DCTX DST CAP SRC src size);
        [ exact DA2 | exact RD0 | exact RD1 | exact RD8 | exact GOT | exact SB | exact OK | exact N0 | exact NLEN | exact N40 | exact RS0 | exact RS1
        | exact DSK | exact RC0 | exact RC40 | exact DNULL | exact DNN | exact RDST | exact FR | exact RLO | exact LO | exact RSP | exact SP16
        | exact S_DC | exact S_DS | exact S_SR | exact S_GT | exact D_DC | exact D_SR | exact SR_DC | exact GT_DC | exact GT_DS | exact MI
        | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity ].
    - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & -> & MU' & WM' & MI' & ST' & DA' & DSK' & RR & ROK).
      unfold zd_dmf_post. do 14 eexists. exists m', r. split; [reflexivity|].
      split; [eapply munch_trans; [exact MU | exact MU']|]. split; [eapply wmono_trans; [exact WM | exact WM']|].
      split; [exact MI'|]. split; [exact ST'|]. split; [exact DA'|]. split; [exact DSK'|]. split; [exact RR| exact ROK].
  Qed.
End DDCTX.

Theorem zd_ddctx_proof : zd_dmf_stmt -> zd_ddctx_stmt.
Proof.
  intros DMF. unfold zd_ddctx_stmt.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SP lo DCTX DST CAP SRC src size
         DA RD0 RD1 RD8 GOT SB OK N0 NLEN N40 RS0 RS1 DSK RC0 RC40 DNULL DNN RDST ST RLO LO RSP SP16
         S_DC S_DS S_SR S_GT D_DC D_SR SR_DC GT_DC GT_DS MI -> -> -> -> ->.
  eapply ddctx_body; eassumption.
Qed.
