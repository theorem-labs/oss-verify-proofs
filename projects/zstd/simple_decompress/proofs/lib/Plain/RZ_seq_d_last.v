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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdDctxRep ZdSeqW KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_d_base.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma p_lastcopy : forall (P : sdp) m1 jpre OP LP LL (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word),
  seqd_ranges P -> seqd_sep P -> seqd_xinv P m1 (seqd_fe P) ->
  rw_cells psegs m1 (q_SPV P + -304) (CB 200 jpre :: seqd_saved P) ->
  q_DST P <= OP -> 0 <= LL -> OP + LL <= q_DST P + q_CAP P -> (OP = 0 -> q_DST P = 0) -> (OP <> 0 -> 4096 <= q_B0 P) ->
  4096 <= LP -> LP + LL < 2^47 -> rdbl psegs m1 LP (LP + LL) -> (LP + LL <= OP \/ OP + LL <= LP) ->
  off_stack (q_lo P) (q_SPV P) LP LL ->
  evt psegs (seqd_post P)
    (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -304)) (q_gp P) (q_tp P) x5 x6 x7 (Z_to_bv 64 (q_DST P)) (Z_to_bv 64 LL) x10 (Z_to_bv 64 LP) x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 (Z_to_bv 64 OP) x25 x26 x27 x28 x29 x30 x31)
        (q_F P) (Z_to_bv 64 0x1c050) (q_fc P) None m1 (seg_rom psegs)).
Proof.
  intros P m1 jpre OP LP LL x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 RG SEP XI FR H1 H2 H3 H4 H5 H6 H7 RDL DJL OSL.
  pose proof (p_exit P) as PEXIT. pose proof RG as RG0. pose proof XI as XI0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_ranges seqd_sep seqd_xinv seqd_post seqd_saved q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in RG, SEP, XI, FR, H1, H3, H4, H5, OSL |- *.
  cbn [q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in PEXIT.
  destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15).
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & MU & WM & MI1).
  destruct SEP as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
  unfold off_stack, apart, DCTX_SIZEOF, WILDCOPY_OVERLENGTH, DCTX_entropy_rep, DCTX_fseEntropy, dctx_h3 in *.
  match goal with |- evt _ ?Q _ => set (PO := Q) end.
  assert (BR : OP <> 0 -> stk psegs m1 OP (OP + LL)) by (intros NZ; eapply stk_sub; [exact BUF| lia| lia| lia]).
  assert (RA : 496 <= SPV < 2^47 /\ 0 <= OP < 2^47 /\ 0 <= DST < 2^47 /\ 0 <= LL < 2^47 /\ 0 <= LP /\ OP + LL < 2^47) by (destruct BUF as (HB & _); lia).
  pose proof RDL as RDL1.
  hold REP. hold HH3. hold BUF. hold STK. hold RDL. hold RG0. hold XI0. hold PEXIT. hold BR.
  hold G1. hold G2. hold G3. hold G4. hold G5. hold G6. hold G7. hold G8. hold G9. hold G10. hold G11. hold G12. hold G13. hold G14. hold G15.
  hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold H1. hold H3. hold H4. hold H5. hold DJL. hold OSL. hold RDL1.
  kx_autoLx [0x1c070] 20%nat [KZRange SPV 496 (2^47); KZRange OP 0 (2^47); KZRange DST 0 (2^47); KZRange LL 0 (2^47)] [].
  - (* [comment removed for export] *)
    unfold held in *.
    assert (OP0 : OP = 0) by (rewrite ?Z.mod_small in KXBR by lia; exact KXBR).
    assert (D0 : DST = 0) by auto. replace (-1 * DST) with 0 by lia.
    subst PO. eapply (PEXIT m1 jpre 0); [exact RG0 | exact XI0 | exact FR | lia | right; lia].
  - unfold held in *. hold BUF. hold RDL.
    assert (OPN : OP <> 0) by (rewrite ?Z.mod_small in KXBR by lia; exact KXBR).
    specialize (BR OPN).
    call (memcpy_call_spec OP LP LL); [exact BR | exact RDL1 | lia | lia | lia | lia | lia | exact DJL | exact KXMI |].
    apply PC in BUF. clear PC POST RDL.
    hold REP. hold HH3. hold BUF. hold STK. hold RG0. hold PEXIT.
    hold G1. hold G2. hold G3. hold G4. hold G5. hold G6. hold G7. hold G8. hold G9. hold G10. hold G11. hold G12. hold G13. hold G14. hold G15.
    hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold H1. hold H3. hold H4. hold H5. hold DJL. hold OSL.
    kx_autoLx [0x1c070] 20%nat [KZRange SPV 496 (2^47); KZRange OP 0 (2^47); KZRange DST 0 (2^47); KZRange LL 0 (2^47)] [].
    unfold held in *.
    replace (-1 * DST + (LL + OP)) with (OP + LL - DST) by lia.
    subst PO. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => eapply (PEXIT mm jpre (OP + LL - DST)) end; [exact RG0 | | exact FR | lia | right; lia].
    cbn [seqd_xinv]. unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy. split; [exists r0', r1', r2'; exact REP|].
    split; [exact HH3|]. split; [exact BUF|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM|]. lazymatch goal with MI : mem_inv psegs ?mm |- mem_inv psegs ?mm => exact MI end.
Qed.
