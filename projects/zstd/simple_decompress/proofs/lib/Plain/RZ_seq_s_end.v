(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma seqs_eframe_exit : forall (P : ssp) (m1 : fmem) ja jb jc dw lw,
  rw_cells psegs m1 (v_SPV P + -336) ([CB 40 ja; C8 dw; CB 32 jb; C8 lw; CB 144 jc] ++ seqs_saved P) ->
  exists jpre, rw_cells psegs m1 (v_SPV P + -336) (CB 232 jpre :: seqs_saved P).
Proof.
  intros P m1 ja jb jc dw lw FR.
  apply (rw_cells_forget _ _ _ 5%nat 232%nat) in FR; [|reflexivity].
  cbn [skipn app] in FR. eexists. exact FR.
Qed.

(* [comment removed for export] *)
Lemma seqs_p_last2 : forall (P : ssp) m1 ja jb jc OEND OP LP LEND loc (x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x27 x28 x29 x30 x31 : word),
  seqs_ranges P -> seqs_sep P -> seqs_xinv P m1 (seqs_fe P) -> h5_viewed m1 (v_DCTX P) (v_ws P) loc ->
  rw_cells psegs m1 (v_SPV P + -336) ([CB 40 ja; C8 (Z_to_bv 64 (v_DST P)); CB 32 jb; C8 (Z_to_bv 64 LEND); CB 144 jc] ++ seqs_saved P) ->
  v_DST P <= OP -> OP <= OEND -> OEND <= v_DST P + v_CAP P ->
  4096 <= LP -> LP <= LEND -> LEND < 2^47 -> rdbl psegs m1 LP LEND -> (LEND <= OP \/ OEND <= LP) ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 x8 x9 x10 (Z_to_bv 64 LP) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 (Z_to_bv 64 OEND) x24 x25 (Z_to_bv 64 OP) x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x199dc) (v_fc P) None m1 (seg_rom psegs)).
Proof.
  intros P m1 ja jb jc OEND OP LP LEND loc x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x27 x28 x29 x30 x31 RG SEP XI H5V FR H1 H2 H3 H4 H5 H6 RDL DJL.
  pose proof (seqs_p_exit P) as PEXIT. pose proof (seqs_eframe_exit P) as EFX. pose proof RG as RG0. pose proof XI as XI0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_ranges seqs_sep seqs_xinv seqs_post seqs_saved v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in RG, SEP, XI, FR, H1, H3, H5V |- *.
  cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in PEXIT, EFX.
  destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & MU & WM & MI1).
  destruct SEP as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
  destruct H5V as (H5C & H5L). unfold h5_vcells in H5C.
  unfold off_stack, apart, DCTX_SIZEOF, WILDCOPY_OVERLENGTH, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, dctx_h3 in *.
  match goal with |- evt _ ?Q _ => set (PO := Q) end.
  assert (RA : 544 <= SPV < 2^47 /\ 4096 <= OP < 2^47 /\ 4096 <= DST < 2^47 /\ 4096 <= OEND < 2^47 /\ 4096 <= LP < 2^47 /\ 4096 <= LEND < 2^47 /\ 0 <= LEND - LP <= 2^47 /\ 0 <= OEND - OP <= 2^47) by lia.
  pose proof RDL as RDL1. cbn [app] in FR.
  hold REP. hold HH3. hold H5C. hold BUF. hold STK. hold RG0. hold XI0. hold PEXIT. hold EFX.
  hold G1. hold G2. hold G3. hold G4. hold G5. hold G6. hold G7. hold G8. hold G9. hold G10. hold G11. hold G12. hold G13. hold G14. hold G15. hold G16.
  hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold RDL. hold H1. hold H2. hold H3. hold H4. hold H5. hold H6. hold DJL. hold RDL1.
  kx_autoLx [0x1a5ec] 30%nat [KZRange SPV 544 (2^47); KZRange OP 4096 (2^47); KZRange DST 4096 (2^47); KZRange OEND 4096 (2^47); KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange (LEND - LP) 0 (2^47); KZRange (OEND - OP) 0 (2^47)] [(SPV - 336, 336)].
  - unfold held in *.
    assert (BR : stk psegs m1 OP (OP + (-1 * LP + LEND))) by (eapply stk_sub; [exact BUF| lia| lia| lia]).
    hold BUF. hold RDL.
    call (memcpy_call_spec OP LP (-1 * LP + LEND)); [exact BR | replace (LP + (-1 * LP + LEND)) with LEND by lia; exact RDL1 | lia | lia | lia | lia | lia | lia | exact KXMI |].
    apply PC in BUF. clear PC POST RDL.
    hold REP. hold HH3. hold H5C. hold BUF. hold STK. hold RG0. hold XI0. hold PEXIT. hold EFX.
  hold G1. hold G2. hold G3. hold G4. hold G5. hold G6. hold G7. hold G8. hold G9. hold G10. hold G11. hold G12. hold G13. hold G14. hold G15. hold G16.
  hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold H1. hold H2. hold H3. hold H4. hold H5. hold H6. hold DJL. hold RDL1.
    kx_autoLx [0x1a5ec] 20%nat [KZRange SPV 544 (2^47); KZRange OP 4096 (2^47); KZRange DST 4096 (2^47); KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange (LEND - LP) 0 (2^47)] [(SPV - 336, 336)].
    unfold held in *.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (EFX mm _ _ _ _ _ FR) as (jpre & FRX); subst PO;
      eapply (PEXIT mm jpre (-1 * LP + (LEND + (OP + -1 * DST))) loc); [exact RG0 | | split; [exact H5C | exact H5L] | exact FRX | lia | right; lia] end.
    cbn [seqs_xinv]. unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation.
    split; [exists r0', r1', r2'; exact REP|]. split; [exact HH3|]. split; [exact BUF|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| exact MI].
  - unfold held in *.
    destruct (EFX m1 _ _ _ _ _ FR) as (jpre & FRX). subst PO.
    eapply (PEXIT m1 jpre 18446744073709551546 loc); [exact RG0 | exact XI0 | split; [exact H5C | exact H5L] | exact FRX | lia | left; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma seqs_p_last1 : forall (P : ssp) m1 ja jb jc OEND OP LP LEND loc (x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x27 x28 x29 x30 x31 : word),
  seqs_ranges P -> seqs_sep P -> seqs_xinv P m1 (seqs_fe P) -> h5_viewed m1 (v_DCTX P) (v_ws P) loc ->
  rw_cells psegs m1 (v_SPV P + -336) ([CB 40 ja; C8 (Z_to_bv 64 (v_DST P)); CB 32 jb; C8 (Z_to_bv 64 LEND); CB 144 jc] ++ seqs_saved P) ->
  v_DST P <= OP -> OP <= OEND -> OEND <= v_DST P + v_CAP P ->
  4096 <= LP -> LP <= LEND -> v_B0 P <= LP -> LEND <= v_B1 P ->
  rdbl psegs m1 (v_DCTX P + 30372) (v_DCTX P + 95940) ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 x8 x9 x10 (Z_to_bv 64 LP) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (v_DCTX P + 29896)) x19 x20 x21 x22 (Z_to_bv 64 OEND) x24 (Z_to_bv 64 (v_DCTX P)) (Z_to_bv 64 OP) x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x19998) (v_fc P) None m1 (seg_rom psegs)).
Proof.
  intros P m1 ja jb jc OEND OP LP LEND loc x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x24 x27 x28 x29 x30 x31 RG SEP XI H5V FR H1 H2 H3 H4 H5 H6 H7 XLIT.
  pose proof (seqs_p_last2 P) as PLAST. pose proof (seqs_p_exit P) as PEXIT. pose proof (seqs_eframe_exit P) as EFX. pose proof RG as RG0. pose proof SEP as SEP0. pose proof XI as XI0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_ranges seqs_sep seqs_xinv seqs_post seqs_saved v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in RG, SEP, XI, FR, H1, H3, H6, H7, H5V, XLIT |- *.
  cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in PEXIT, EFX, PLAST.
  destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & MU & WM & MI1).
  destruct SEP as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
  destruct H5V as (H5C & H5L). unfold h5_vcells in H5C.
  unfold off_stack, apart, DCTX_SIZEOF, WILDCOPY_OVERLENGTH, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, dctx_h3 in *.
  match goal with |- evt _ ?Q _ => set (PO := Q) end.
  assert (RA : 544 <= SPV < 2^47 /\ 4096 <= OP < 2^47 /\ 4096 <= DST < 2^47 /\ 4096 <= OEND < 2^47 /\ 4096 <= LP < 2^47 /\ 4096 <= LEND < 2^47 /\ 0 <= LEND - LP <= 2^47 /\ 0 <= OEND - OP <= 2^47 /\ 4096 <= DCTX < 2^47) by lia.
  cbn [app] in FR.
  hold REP. hold HH3. hold H5C. hold BUF. hold STK. hold RG0. hold XI0. hold PEXIT. hold EFX.
  hold G1. hold G2. hold G3. hold G4. hold G5. hold G6. hold G7. hold G8. hold G9. hold G10. hold G11. hold G12. hold G13. hold G14. hold G15. hold G16.
  hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold PLAST. hold SEP0. hold XLIT. hold H1. hold H2. hold H3. hold H4. hold H5. hold H6. hold H7.
  kx_autoLx [0x1a5ec; 0x199dc] 30%nat [KZRange SPV 544 (2^47); KZRange OP 4096 (2^47); KZRange DST 4096 (2^47); KZRange OEND 4096 (2^47); KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange (LEND - LP) 0 (2^47); KZRange (OEND - OP) 0 (2^47)] [(SPV - 336, 336)].
  - unfold held in *.
    destruct (EFX m1 _ _ _ _ _ FR) as (jpre & FRX). subst PO.
    eapply (PEXIT m1 jpre 18446744073709551546 loc); [exact RG0 | exact XI0 | split; [exact H5C | exact H5L] | exact FRX | lia | left; reflexivity].
  - unfold held in *.
    assert (BR : stk psegs m1 OP (OP + (-1 * LP + LEND))) by (eapply stk_sub; [exact BUF| lia| lia| lia]).
    assert (RDS : rdbl psegs m1 LP (LP + (-1 * LP + LEND))) by (eapply rdbl_sub; [eapply rdbl_of_stk; exact BUF | lia | lia]).
    hold BUF. hold XLIT.
    call (memmove_call_spec OP LP (-1 * LP + LEND)); [exact BR | exact RDS | lia | lia | lia | lia | lia | exact KXMI |].
    apply PC in BUF. apply POST in XLIT. clear PC POST.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (MUL : munch [(DCTX + 30368, DCTX + 30368 + 4); (SPV - 336, SPV)] mm mm) by apply munch_refl end.
    assert (DJD : SPV - 336 + 336 <= DCTX \/ DCTX + 95992 <= SPV - 336) by lia.
    hold RG0. hold XI0. hold PEXIT. hold EFX. hold PLAST. hold SEP0. hold XLIT.
    hold G1. hold G2. hold G3. hold G4. hold G5. hold G6. hold G7. hold G8. hold G9. hold G10. hold G11. hold G12. hold G13. hold G14. hold G15. hold G16.
    hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold H1. hold H2. hold H3. hold H4. hold H5. hold H6. hold H7. hold RDS.
    kx_autoLx [0x199dc] 30%nat [KZRange SPV 544 (2^47); KZRange OP 4096 (2^47); KZRange DCTX 4096 (2^47); KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange (LEND - LP) 0 (2^47); KZWr (SPV - 336) 336; KZWr (DCTX + 30096) 276; KZDisj (SPV - 336) 336 DCTX 95992] [(SPV - 336, 336)].
    kx_mem. unfold held in *.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (XL2 : rdbl psegs mm (DCTX + 30372) (DCTX + 95940)) by (eapply rdbl_transport; [exact XLIT | exact MUL | intros x' Hx; left; cbn [outside]; split; [lia| split; [lia| exact I]]]);
      subst PO;
      eapply (PLAST mm ja jb jc OEND (-1 * LP + (LEND + OP)) (DCTX + 30372) (DCTX + 95908) (Z_to_bv 64 0)); [exact RG0 | exact SEP0 | | split; [exact H5C|exact H5L] | exact FR | lia | lia | lia | lia | lia | lia | eapply rdbl_sub; [exact XL2 | lia | lia] | lia] end.
    cbn [seqs_xinv]. unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation.
    split; [exists r0', r1', r2'; exact REP|]. split; [exact HH3|]. split; [exact BUF|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| exact KXMI].
Qed.
