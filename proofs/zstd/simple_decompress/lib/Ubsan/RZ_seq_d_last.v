(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdDctxRep ZdSeqW KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_d_base.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma p_lastcopy : forall (P : sdp) m1 jpre jmid OP LP LL (x1 x5 x6 x7 x8 x10 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word),
  seqd_ranges P -> seqd_sep P -> seqd_xinv P m1 (seqd_fe P) ->
  rw_cells usegs m1 (q_SPV P + -352) (CB 32 jpre :: C8 (Z_to_bv 64 (q_DST P)) :: CB 208 jmid :: seqd_saved P) ->
  q_DST P <= OP -> 0 <= LL -> OP + LL <= q_DST P + q_CAP P -> (OP = 0 -> q_DST P = 0) -> (OP <> 0 -> 4096 <= q_B0 P) ->
  4096 <= LP -> LP + LL < 2^47 -> rdbl usegs m1 LP (LP + LL) -> (LP + LL <= OP \/ OP + LL <= LP) ->
  off_stack (q_lo P) (q_SPV P) LP LL ->
  evt usegs (seqd_post P)
    (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -352)) (q_gp P) (q_tp P) x5 x6 x7 x8 (Z_to_bv 64 LL) x10 (Z_to_bv 64 LP) (Z_to_bv 64 (q_DST P)) x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 OP) x27 x28 x29 x30 x31)
        (q_F P) (Z_to_bv 64 0x1d6b0) (q_fc P) None m1 (seg_rom usegs)).
Proof.
  intros P m1 jpre jmid OP LP LL x1 x5 x6 x7 x8 x10 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 RG SEP XI FR H1 H2 H3 H4 H5 H6 H7 RDL DJL OSL.
  pose proof (p_exit P) as PEXIT. pose proof RG as RG0. pose proof XI as XI0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_ranges seqd_sep seqd_xinv seqd_post seqd_saved q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in RG, SEP, XI, FR, H1, H3, H4, H5, OSL |- *.
  cbn [q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in PEXIT.
  destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15).
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & MU & WM & MI1).
  destruct SEP as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
  unfold off_stack, apart, DCTX_SIZEOF, WILDCOPY_OVERLENGTH, DCTX_entropy_rep, DCTX_fseEntropy, dctx_h3 in *.
  match goal with |- evt _ ?Q _ => set (PO := Q) end.
  assert (BR : OP <> 0 -> stk usegs m1 OP (OP + LL)) by (intros NZ; eapply stk_sub; [exact BUF| lia| lia| lia]).
  assert (RA : 544 <= SPV < 2^47 /\ 0 <= OP < 2^47 /\ 0 <= DST < 2^47 /\ 0 <= LL < 2^47 /\ 0 <= LP /\ OP + LL < 2^47) by (destruct BUF as (HB & _); lia).
  pose proof RDL as RDL1.
  hold REP. hold HH3. hold BUF. hold STK. hold RDL. hold RG0. hold XI0. hold PEXIT. hold BR.
  hold G1. hold G2. hold G3. hold G4. hold G5. hold G6. hold G7. hold G8. hold G9. hold G10. hold G11. hold G12. hold G13. hold G14. hold G15.
  hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold H1. hold H3. hold H4. hold H5. hold DJL. hold OSL. hold RDL1.
  kx_autoLx [0x1d6e4] 20%nat [KZRange SPV 544 (2^47); KZRange OP 0 (2^47); KZRange DST 0 (2^47); KZRange LL 0 (2^47)] [].
  - (* [comment removed for export] *)
    unfold held in *.
    assert (OP0 : OP = 0) by (rewrite ?Z.mod_small in KXBR by lia; exact KXBR).
    assert (D0 : DST = 0) by auto.
    pose proof (rw_cells_forget _ _ _ 3%nat 248%nat FR eq_refl) as FRX. cbn [firstn skipn] in FRX.
    subst PO. lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?r) _ _ _ _ _ _) _ _ _ _ _ _) =>
      eapply (PEXIT m1 _ r); [exact RG0 | exact XI0 | exact FRX | lia | right; lia] end.
  - unfold held in *. hold BUF. hold RDL.
    assert (OPN : OP <> 0) by (rewrite ?Z.mod_small in KXBR by lia; exact KXBR).
    specialize (BR OPN).
    call (memcpy_call_spec OP LP LL); [exact BR | exact RDL1 | lia | lia | lia | lia | lia | exact DJL | exact KXMI |].
    apply PC in BUF. clear PC POST RDL.
    hold REP. hold HH3. hold BUF. hold STK. hold RG0. hold PEXIT.
    hold G1. hold G2. hold G3. hold G4. hold G5. hold G6. hold G7. hold G8. hold G9. hold G10. hold G11. hold G12. hold G13. hold G14. hold G15.
    hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold H1. hold H3. hold H4. hold H5. hold DJL. hold OSL.
    kx_autoLx [0x1d6e4] 20%nat [KZRange SPV 544 (2^47); KZRange OP 0 (2^47); KZRange DST 0 (2^47); KZRange LL 0 (2^47)] [].
    all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d724) _ _ _ _) => kx_trap_fast | _ => idtac end.
    unfold held in *.
    pose proof (rw_cells_forget _ _ _ 3%nat 248%nat FR eq_refl) as FRX. cbn [firstn skipn] in FRX.
    subst PO. lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?r) _ _ _ _ _ _) _ _ _ _ ?mm _) =>
      eapply (PEXIT mm _ r); [exact RG0 | | exact FRX | lia | right; lia] end.
    cbn [seqd_xinv]. unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy. split; [exists r0', r1', r2'; exact REP|].
    split; [exact HH3|]. split; [exact BUF|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM|]. lazymatch goal with MI : mem_inv usegs ?mm |- mem_inv usegs ?mm => exact MI end.
Qed.
