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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_d_base RZ_seq_d_lbase RZ_seq_d_lkit RZ_seq_d_ibase.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seqd_static_intro : forall P OEND LEND,
  seqd_ranges P -> seqd_side P -> seqd_sep P -> seqd_tables P -> q_nbSeq P <> 0 -> 1 <= zlen (q_sq P) ->
  LEND = q_LITP P + q_LITSZ P ->
  ((q_LOC P = 0 /\ OEND = q_DST P + q_CAP P) \/ (q_LOC P = 1 /\ OEND = q_LITB P)) ->
  seqd_static P OEND LEND.
Proof.
  intros P OEND LEND RG SD SEP TB NZ N1 EL EO.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_static seqd_ranges seqd_side seqd_sep seqd_tables q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in *.
  destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15).
  destruct SD as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8).
  destruct SEP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  destruct TB as ((_ & OKLL) & (_ & OKOF) & (_ & OKML) & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & _).
  unfold off_stack, apart, DCTX_SIZEOF, WILDCOPY_OVERLENGTH, ZSTD_not_in_dst, ZSTD_in_dst in *.
  assert (DN : DST <> 0) by (intros E; destruct (D3 E) as (_ & E2); contradiction).
  specialize (D4 DN). specialize (D5 NZ). clear D3 D6.
  assert (OE : DST <= OEND <= DST + CAP /\ ((OEND <= LITP /\ LEND + 32 <= B1) \/ LEND + 32 <= B0 \/ B1 <= LITP)).
  { destruct EO as [(L0 & ->)|(L1 & ->)].
    - specialize (D8 L0). clear - D8 G8 EL G10. lia.
    - specialize (D7 L1). clear - D7 EL. lia. }
  destruct OE as (OE1 & OE2). clear D7 D8 EO.
  repeat (split; [first [assumption | clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 D4 D5 OE1 EL N1 NZ; lia]|]).
  split; [clear - P2; lia|]. split; [clear - P3; lia|]. split; [clear - P4 EL; lia|]. split; [clear - P1; lia|].
  split; [clear - T7; lia|]. split; [clear - T8; lia|]. split; [clear - T9; lia|].
  split; [clear - P6; lia|]. split; [clear - P5; lia|].
  split; [clear - T10; lia|]. split; [clear - T11; lia|]. split; [clear - T12; lia|].
  split; [exact OKLL|]. split; [exact OKOF| exact OKML].
Qed.

(* [comment removed for export] *)
Lemma seqd_iexit : forall P LEND m1 fr r (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word),
  seqd_ranges P -> seqd_iinv P LEND m1 fr -> cells_size (firstn 24 fr) = 200%nat -> skipn 24 fr = [CB 104 (le8 (q_s11 P) ++ le8 (q_s10 P) ++ le8 (q_s9 P) ++ le8 (q_s8 P) ++ le8 (q_s7 P) ++ le8 (q_s6 P) ++ le8 (q_s5 P) ++ le8 (q_s4 P) ++ le8 (q_s3 P) ++ le8 (q_s2 P) ++ le8 (q_s1 P) ++ le8 (q_s0 P) ++ le8 (q_ra P))] ->
  0 <= r < 2^64 -> (zd_is_error r = true \/ r <= q_CAP P) ->
  evt psegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -304)) (q_gp P) (q_tp P) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 r) x27 x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1c070) (q_fc P) None m1 (seg_rom psegs)).
Proof.
  intros P LEND m1 fr r x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 RG (FR & _ & _ & _ & _ & _ & _ & XI) SZ SK HR RES.
  apply (rw_cells_forget _ _ _ 24%nat 200%nat) in FR; [|exact SZ]. rewrite SK in FR.
  set (X := cells_bytes _) in FR. clearbody X.
  assert (FRX : rw_cells psegs m1 (q_SPV P + -304) (CB 200 X :: seqd_saved P)).
  { pose proof FR as [[WF _] _]. cbn [cells_wf cell_wf] in WF. destruct WF as (WX & _).
    eapply rw_cells_recell; [exact FR | | ].
    - clear - WX. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seqd_saved cells_wf cell_wf]. split; [exact WX|]. repeat split.
    - clear. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seqd_saved cells_bytes cbytes q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws]. rewrite !app_nil_r. reflexivity. }
  eapply (p_exit P m1 X r); [exact RG | exact XI | exact FRX | exact HR | exact RES].
Qed.

(* [comment removed for export] *)
Definition ai_1ac (P : sdp) (OEND LEND : Z) : Prop :=
  forall (m1 : fmem) (p0 p1 p2 : word) (j0 jpad jseq j_c8 j_c16 j_c24 j_c48 j_cw j_cbc j_cptr j_c80 j_c88 j_c96 j_c104 j_c112 j_c120 j_c128 j_c136 : list byte)
         (t5v r10 : Z) (x1 x5 x6 x7 x11 x12 x15 x16 x17 x19 x20 x21 x22 x23 x25 x28 x31 : word),
  seqd_iinv P LEND m1 [CB 8 j0; CB 8 j_c8; CB 8 j_c16; CB 8 j_c24; C8 (q_dend P); C8 (Z_to_bv 64 (q_PFX P)); CB 8 j_c48; CB 8 j_cw; CB 4 j_cbc; CB 4 jpad; CB 8 j_cptr; CB 8 j_c80; CB 8 j_c88; CB 8 j_c96; CB 8 j_c104; CB 8 j_c112; CB 8 j_c120; CB 8 j_c128; CB 8 j_c136; C8 p0; C8 p1; C8 p2; C8 (Z_to_bv 64 (q_LITP P)); CB 24 jseq; CB 104 (le8 (q_s11 P) ++ le8 (q_s10 P) ++ le8 (q_s9 P) ++ le8 (q_s8 P) ++ le8 (q_s7 P) ++ le8 (q_s6 P) ++ le8 (q_s5 P) ++ le8 (q_s4 P) ++ le8 (q_s3 P) ++ le8 (q_s2 P) ++ le8 (q_s1 P) ++ le8 (q_s0 P) ++ le8 (q_ra P))] ->
  t5v = q_DCTX P + 26684 -> r10 = 2^64 - 20 ->
  evt psegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -304)) (q_gp P) (q_tp P) x5 x6 x7 (Z_to_bv 64 (q_DST P)) (Z_to_bv 64 (q_PFX P)) (Z_to_bv 64 (q_DCTX P)) x11 x12 (Z_to_bv 64 (q_SEQ P)) (Z_to_bv 64 (zlen (q_sq P))) x15 x16 x17 (Z_to_bv 64 (q_nbSeq P)) x19 x20 x21 x22 x23 (Z_to_bv 64 (q_DST P)) x25 (Z_to_bv 64 r10) (Z_to_bv 64 LEND) x28 (Z_to_bv 64 OEND) (Z_to_bv 64 t5v) x31) (q_F P) (Z_to_bv 64 0x1b278) (q_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Lemma prologue_frame : forall (m : fmem) A j (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word),
  rw_cells psegs m A (CB 200 j :: [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) ->
  exists j0 j_c8 j_c16 j_c24 j_c32 j_c40 j_c48 j_cw j_cbc jpad j_cptr j_c80 j_c88 j_c96 j_c104 j_c112 j_c120 j_c128 j_c136 j_p0 j_p1 j_p2 j_c168 jseq,
    rw_cells psegs m A [CB 8 j0; CB 8 j_c8; CB 8 j_c16; CB 8 j_c24; CB 8 j_c32; CB 8 j_c40; CB 8 j_c48; CB 8 j_cw; CB 4 j_cbc; CB 4 jpad; CB 8 j_cptr; CB 8 j_c80; CB 8 j_c88; CB 8 j_c96; CB 8 j_c104; CB 8 j_c112; CB 8 j_c120; CB 8 j_c128; CB 8 j_c136; CB 8 j_p0; CB 8 j_p1; CB 8 j_p2; CB 8 j_c168; CB 24 jseq; CB 104 (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++ le8 s1 ++ le8 s0 ++ le8 ra)].
Proof.
  intros m A j s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra FR.
  change (rw_cells psegs m A ([CB 200 j] ++ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ++ [])) in FR.
  apply rw_cells_merge in FR. cbn [cells_size csize Nat.add cells_bytes cbytes] in FR. rewrite !app_nil_r in FR.
  change (rw_cells psegs m A ([] ++ CB 200 j :: [CB 104 (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++ le8 s1 ++ le8 s0 ++ le8 ra)])) in FR.
  apply (rw_cells_split_CB psegs m A [] 200 j _ [8; 8; 8; 8; 8; 8; 8; 8; 4; 4; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 24]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells] in FR. do 24 eexists. exact FR.
Qed.
