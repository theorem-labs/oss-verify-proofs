(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl ZdCellKit KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma seql_eframe_exit : forall (P : slp) (m1 : fmem) ja d jb oe jc lw jd,
  rw_cells usegs m1 (y_SPV P + -688) ([CB 96 ja; C8 d; CB 56 jb; C8 oe; CB 72 jc; C8 lw; CB 336 jd] ++ seql_saved P) ->
  exists jpre, rw_cells usegs m1 (y_SPV P + -688) (CB 584 jpre :: seql_saved P).
Proof.
  intros P m1 ja d jb oe jc lw jd FR.
  apply (rw_cells_forget _ _ _ 7%nat 584%nat) in FR; [|reflexivity].
  cbn [skipn app] in FR. eexists. exact FR.
Qed.

Lemma seql_eframe_carve : forall (A : Z) (m1 : fmem) ja d jb oe jc lw jd (sv : list cell),
  rw_cells usegs m1 A (CB 96 ja :: C8 d :: CB 56 jb :: C8 oe :: CB 72 jc :: C8 lw :: CB 336 jd :: sv) ->
  exists j1 w j3, rw_cells usegs m1 A (CB 96 ja :: C8 d :: CB 56 jb :: C8 oe :: CB 72 jc :: C8 lw :: CB 304 j1 :: C8 w :: CB 24 j3 :: sv).
Proof.
  intros A m1 ja d jb oe jc lw jd sv FR.
  pose proof (rw_cells_split_CB usegs m1 A [CB 96 ja; C8 d; CB 56 jb; C8 oe; CB 72 jc; C8 lw] 336%nat jd sv [304%nat; 8%nat; 24%nat] FR eq_refl) as S.
  cbn [app mk_CB_cells] in S.
  destruct (cb8_as_c8 usegs m1 A [CB 96 ja; C8 d; CB 56 jb; C8 oe; CB 72 jc; C8 lw; CB 304 (firstn 304 jd)] (firstn 8 (skipn 304 jd)) (CB 24 (firstn 24 (skipn 8 (skipn 304 jd))) :: sv) S) as (w & FC).
  exists (firstn 304 jd), w, (firstn 24 (skipn 8 (skipn 304 jd))). exact FC.
Qed.

Lemma seql_eframe_uncarve : forall (A : Z) (m1 : fmem) ja d jb oe jc lw j1 w j3 (sv : list cell),
  rw_cells usegs m1 A (CB 96 ja :: C8 d :: CB 56 jb :: C8 oe :: CB 72 jc :: C8 lw :: CB 304 j1 :: C8 w :: CB 24 j3 :: sv) ->
  exists jd, rw_cells usegs m1 A (CB 96 ja :: C8 d :: CB 56 jb :: C8 oe :: CB 72 jc :: C8 lw :: CB 336 jd :: sv).
Proof.
  intros A m1 ja d jb oe jc lw j1 w j3 sv FR.
  pose proof (rw_cells_merge usegs m1 A [CB 96 ja; C8 d; CB 56 jb; C8 oe; CB 72 jc; C8 lw] [CB 304 j1; C8 w; CB 24 j3] sv FR) as M.
  exists (cells_bytes [CB 304 j1; C8 w; CB 24 j3]). exact M.
Qed.

(* [comment removed for export] *)
Lemma seql_p_last2 : forall (P : slp) m1 ja jb jc jd OEND OP LP LEND loc (x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
  seql_ranges P -> seql_sep P -> seql_xinv P m1 (seql_fe P) -> h5_viewed m1 (y_DCTX P) (y_ws P) loc ->
  rw_cells usegs m1 (y_SPV P + -688) ([CB 96 ja; C8 (Z_to_bv 64 (y_DST P)); CB 56 jb; C8 (Z_to_bv 64 OEND); CB 72 jc; C8 (Z_to_bv 64 LEND); CB 336 jd] ++ seql_saved P) ->
  y_DST P <= OP -> OP <= OEND -> OEND <= y_DST P + y_CAP P ->
  4096 <= LP -> LP <= LEND -> LEND < 2^47 -> rdbl usegs m1 LP LEND ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 x8 x9 x10 (Z_to_bv 64 LP) x12 x13 x14 x15 (Z_to_bv 64 (y_DST P)) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 OP) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x1ab6c) (y_fc P) None m1 (seg_rom usegs)).
Proof.
  intros P m1 ja jb jc jd OEND OP LP LEND loc x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 RG SEP XI H5V FR H1 H2 H3 H4 H5 H6 RDL.
  pose proof (seql_p_exit P) as PEXIT. pose proof (seql_eframe_exit P) as EFX. pose proof RG as RG0. pose proof XI as XI0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_ranges seql_sep seql_xinv seql_post seql_saved y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in RG, SEP, XI, FR, H1, H3, H5V |- *.
  cbn [y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in PEXIT, EFX.
  destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & MU & WM & MI1).
  destruct SEP as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
  destruct H5V as (H5C & H5L). unfold h5_vcells in H5C.
  unfold off_stack, apart, DCTX_SIZEOF, WILDCOPY_OVERLENGTH, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, dctx_h3 in *.
  match goal with |- evt _ ?Q _ => set (PO := Q) end.
  assert (RA : 896 <= SPV < 2^47 /\ 4096 <= OP < 2^47 /\ 4096 <= DST < 2^47 /\ 4096 <= OEND < 2^47 /\ 4096 <= LP < 2^47 /\ 4096 <= LEND < 2^47 /\ 0 <= LEND - LP <= 2^47 /\ 0 <= OEND - OP <= 2^47) by lia.
  pose proof RDL as RDL1. cbn [app] in FR.
  hold REP. hold HH3. hold H5C. hold BUF. hold STK. hold RG0. hold XI0. hold PEXIT. hold EFX.
  hold G1. hold G2. hold G3. hold G4. hold G5. hold G6. hold G7. hold G8. hold G9. hold G10. hold G11. hold G12. hold G13. hold G14. hold G15. hold G16.
  hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold RDL. hold H1. hold H2. hold H3. hold H4. hold H5. hold H6. hold RDL1.
  kx_autoLx [0x1abb4; 0x1ac04] 30%nat [KZRange SPV 896 (2^47); KZRange OP 4096 (2^47); KZRange DST 4096 (2^47); KZRange OEND 4096 (2^47); KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange (LEND - LP) 0 (2^47); KZRange (OEND - OP) 0 (2^47)] [(SPV - 688, 688)].
  all: unfold held in *.
  all: lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1abb4) _ _ _ _) =>
    destruct (EFX m1 _ _ _ _ _ _ _ FR) as (jpre & FRX); subst PO;
    eapply (PEXIT m1 jpre 18446744073709551546 loc); [exact RG0 | exact XI0 | split; [exact H5C | exact H5L] | exact FRX | lia | left; reflexivity]
  | |- _ => idtac end.
  assert (BR : stk usegs m1 OP (OP + (-1 * LP + LEND))) by (eapply stk_sub; [exact BUF| lia| lia| lia]).
  hold BUF. hold RDL.
  call (memmove_call_spec OP LP (-1 * LP + LEND)); [exact BR | replace (LP + (-1 * LP + LEND)) with LEND by lia; exact RDL1 | lia | lia | lia | lia | lia | exact KXMI |].
  apply PC in BUF. clear PC POST RDL.
  hold REP. hold HH3. hold H5C. hold BUF. hold STK. hold RG0. hold XI0. hold PEXIT. hold EFX.
  hold G1. hold G2. hold G3. hold G4. hold G5. hold G6. hold G7. hold G8. hold G9. hold G10. hold G11. hold G12. hold G13. hold G14. hold G15. hold G16.
  hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold H1. hold H2. hold H3. hold H4. hold H5. hold H6. hold RDL1.
  kx_autoLx [0x1abb4; 0x1ac04] 20%nat [KZRange SPV 896 (2^47); KZRange OP 4096 (2^47); KZRange DST 4096 (2^47); KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange (LEND - LP) 0 (2^47)] [(SPV - 688, 688)].
  all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end).
  unfold held in *.
  lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?rr) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ ?mm _) => destruct (EFX mm _ _ _ _ _ _ _ FR) as (jpre & FRX); subst PO;
    eapply (PEXIT mm jpre rr loc); [exact RG0 | | split; [exact H5C | exact H5L] | exact FRX | lia | right; lia] end.
  cbn [seql_xinv]. unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation.
  split; [exists r0', r1', r2'; exact REP|]. split; [exact HH3|]. split; [exact BUF|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| exact MI].
Qed.

(* [comment removed for export] *)
Lemma seql_p_last1 : forall (P : slp) m1 ja jb jc jd OEND OP LP LEND loc (x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
  seql_ranges P -> seql_sep P -> seql_xinv P m1 (seql_fe P) -> h5_viewed m1 (y_DCTX P) (y_ws P) loc ->
  rw_cells usegs m1 (y_SPV P + -688) ([CB 96 ja; C8 (Z_to_bv 64 (y_DST P)); CB 56 jb; C8 (Z_to_bv 64 OEND); CB 72 jc; C8 (Z_to_bv 64 LEND); CB 336 jd] ++ seql_saved P) ->
  y_DST P <= OP -> OP <= OEND -> OEND <= y_DST P + y_CAP P ->
  4096 <= LP -> LP <= LEND -> y_B0 P <= LP -> LEND <= y_B1 P ->
  rdbl usegs m1 (y_DCTX P + 30372) (y_DCTX P + 95940) ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 x8 x9 x10 (Z_to_bv 64 LP) x12 x13 x14 x15 x16 (Z_to_bv 64 (y_DCTX P)) x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 OP) x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x18330) (y_fc P) None m1 (seg_rom usegs)).
Proof.
  intros P m1 ja jb jc jd OEND OP LP LEND loc x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 RG SEP XI H5V FR H1 H2 H3 H4 H5 H6 H7 XLIT.
  pose proof (seql_p_last2 P) as PLAST. pose proof (seql_p_exit P) as PEXIT. pose proof (seql_eframe_exit P) as EFX. pose proof RG as RG0. pose proof SEP as SEP0. pose proof XI as XI0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_ranges seql_sep seql_xinv seql_post seql_saved y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in RG, SEP, XI, FR, H1, H3, H6, H7, H5V, XLIT |- *.
  cbn [y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in PEXIT, EFX, PLAST.
  destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & MU & WM & MI1).
  destruct SEP as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
  destruct H5V as (H5C & H5L). unfold h5_vcells in H5C.
  unfold off_stack, apart, DCTX_SIZEOF, WILDCOPY_OVERLENGTH, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, dctx_h3 in *.
  match goal with |- evt _ ?Q _ => set (PO := Q) end.
  assert (RA : 896 <= SPV < 2^47 /\ 4096 <= OP < 2^47 /\ 4096 <= DST < 2^47 /\ 4096 <= OEND < 2^47 /\ 4096 <= LP < 2^47 /\ 4096 <= LEND < 2^47 /\ 0 <= LEND - LP <= 2^47 /\ 0 <= OEND - OP <= 2^47 /\ 4096 <= DCTX < 2^47) by lia.
  cbn [app] in FR.
  hold REP. hold HH3. hold H5C. hold BUF. hold STK. hold RG0. hold XI0. hold PEXIT. hold EFX.
  hold G1. hold G2. hold G3. hold G4. hold G5. hold G6. hold G7. hold G8. hold G9. hold G10. hold G11. hold G12. hold G13. hold G14. hold G15. hold G16.
  hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold PLAST. hold SEP0. hold XLIT. hold H1. hold H2. hold H3. hold H4. hold H5. hold H6. hold H7.
  kx_autoLx [0x1abb4; 0x1ab6c; 0x1ac04] 30%nat [KZRange SPV 896 (2^47); KZRange OP 4096 (2^47); KZRange DST 4096 (2^47); KZRange OEND 4096 (2^47); KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange (LEND - LP) 0 (2^47); KZRange (OEND - OP) 0 (2^47)] [(SPV - 688, 688)].
  all: unfold held in *.
  all: lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1abb4) _ _ _ _) =>
    destruct (EFX m1 _ _ _ _ _ _ _ FR) as (jpre & FRX); subst PO;
    eapply (PEXIT m1 jpre 18446744073709551546 loc); [exact RG0 | exact XI0 | split; [exact H5C | exact H5L] | exact FRX | lia | left; reflexivity]
  | |- _ => idtac end.
  assert (BR : stk usegs m1 OP (OP + (-1 * LP + LEND))) by (eapply stk_sub; [exact BUF| lia| lia| lia]).
  assert (RDS : rdbl usegs m1 LP (LP + (-1 * LP + LEND))) by (eapply rdbl_sub; [eapply rdbl_of_stk; exact BUF | lia | lia]).
  hold BUF. hold XLIT.
  call (memmove_call_spec OP LP (-1 * LP + LEND)); [exact BR | exact RDS | lia | lia | lia | lia | lia | exact KXMI |].
  apply PC in BUF. apply POST in XLIT. clear PC POST.
  destruct (seql_eframe_carve _ _ _ _ _ _ _ _ _ _ FR) as (cj1 & cw & cj3 & FRC). clear FR. rename FRC into FR.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (MUL : munch [(SPV - 688, SPV)] mm mm) by apply munch_refl end.
  assert (DJD : SPV - 688 + 688 <= DCTX \/ DCTX + 95992 <= SPV - 688) by lia.
  hold RG0. hold XI0. hold PEXIT. hold EFX. hold PLAST. hold SEP0. hold XLIT.
  hold G1. hold G2. hold G3. hold G4. hold G5. hold G6. hold G7. hold G8. hold G9. hold G10. hold G11. hold G12. hold G13. hold G14. hold G15. hold G16.
  hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold H1. hold H2. hold H3. hold H4. hold H5. hold H6. hold H7. hold RDS.
  kx_autoLx [0x1ab6c; 0x1ac04] 30%nat [KZRange SPV 896 (2^47); KZRange OP 4096 (2^47); KZRange DCTX 4096 (2^47); KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange (LEND - LP) 0 (2^47); KZWr (SPV - 688) 688; KZDisj (SPV - 688) 688 DCTX 95992] [(SPV - 688, 688)].
  all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end).
  kx_mem. unfold held in *.
  destruct (seql_eframe_uncarve _ _ _ _ _ _ _ _ _ _ _ _ FR) as (jd2 & FRU).
  lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?op2) _ _ _ _) _ _ _ _ ?mm _) =>
    assert (XL2 : rdbl usegs mm (DCTX + 30372) (DCTX + 95940)) by (eapply rdbl_transport; [exact XLIT | exact MUL | intros x' Hx; left; cbn [outside]; split; [lia| exact I]]);
    subst PO;
    eapply (PLAST mm ja jb jc jd2 OEND op2 (DCTX + 30372) (DCTX + 95908) loc); [exact RG0 | exact SEP0 | | split; [exact H5C|exact H5L] | exact FRU | lia | lia | lia | lia | lia | lia | eapply rdbl_sub; [exact XL2 | lia | lia]] end.
  cbn [seql_xinv]. unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation.
  split; [exists r0', r1', r2'; exact REP|]. split; [exact HH3|]. split; [exact BUF|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| exact KXMI].
Qed.
