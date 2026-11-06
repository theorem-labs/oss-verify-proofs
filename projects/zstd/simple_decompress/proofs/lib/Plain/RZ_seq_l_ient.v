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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost StrFun ZdCellKit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_ibase.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma cb4_as_c4 : forall (m : fmem) A pre j post,
  rw_cells psegs m A (pre ++ CB 4 j :: post) -> exists w, rw_cells psegs m A (pre ++ C4 w :: post).
Proof.
  intros m A pre j post H. exists (le_bytes_to_word j).
  pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [WF1 [WFJ WF2]]. cbn in WFJ.
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact WF1|]. split; [exact I| exact WF2].
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. f_equal. f_equal.
    unfold le4, word_to_le_bytes, le_bytes_to_word.
    pose proof (le_val_range _ (bytes_ok_map j)) as HR. rewrite length_map, WFJ in HR.
    change (256 ^ Z.of_nat 4) with (2^32) in HR. rewrite <- bytes_le_to_Z_le_val in HR.
    rewrite unsigned_lit by lia. rewrite <- WFJ. apply Z_to_le_bytes_to_Z.
Qed.

(* [comment removed for export] *)
Definition pick8 (j a0 a1 a2 a3 a4 a5 a6 a7 : Z) : Z :=
  if j =? 0 then a0 else if j =? 1 then a1 else if j =? 2 then a2 else if j =? 3 then a3 else if j =? 4 then a4 else if j =? 5 then a5 else if j =? 6 then a6 else a7.
Lemma seql_ring_any : forall l : list byte, length l = 192%nat -> exists rl rm ro, seql_ring_bytes rl rm ro = l.
Proof.
  intros l HL.
  set (w := fun k : nat => bv_unsigned (le_bytes_to_word (firstn 8 (skipn k l)))).
  exists (fun j => pick8 j (w 0%nat) (w 24%nat) (w 48%nat) (w 72%nat) (w 96%nat) (w 120%nat) (w 144%nat) (w 168%nat)),
         (fun j => pick8 j (w 8%nat) (w 32%nat) (w 56%nat) (w 80%nat) (w 104%nat) (w 128%nat) (w 152%nat) (w 176%nat)),
         (fun j => pick8 j (w 16%nat) (w 40%nat) (w 64%nat) (w 88%nat) (w 112%nat) (w 136%nat) (w 160%nat) (w 184%nat)).
  unfold seql_ring_bytes, pick8, w. cbn [Z.eqb Pos.eqb]. rewrite !Z_to_bv_bv_unsigned.
  do 192 (destruct l as [|? l]; [discriminate HL|]). destruct l; [|discriminate HL].
  cbn [firstn skipn]. rewrite !le8_of_bytes by reflexivity. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma evt_s3 : forall (Q : machine_state -> Prop) x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x19' x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F pc fc (m : fmem),
  x19 = x19' ->
  evt psegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19' x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc None m (seg_rom psegs)) ->
  evt psegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc None m (seg_rom psegs)).
Proof. intros. subst. assumption. Qed.

(* [comment removed for export] *)
Lemma seql_static_m2 : forall P OEND,
  seql_ranges P -> seql_side P -> seql_sep P -> seql_tables P -> y_nbSeq P <> 0 -> 1 <= zlen (y_sq P) ->
  y_LOC P = 2 -> OEND = y_DST P + y_CAP P ->
  seql_static P OEND (y_LITP P) (y_LBE P) 2.
Proof.
  intros P OEND RG SD SEP TB NZ N1 EL EO.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_ranges seql_side seql_sep seql_tables y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in *.
  destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
  destruct SD as (D1 & D2 & D3 & D4 & D5).
  destruct SEP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  destruct TB as ((_ & OKLL) & (_ & OKOF) & (_ & OKML) & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15).
  unfold seq_lit_placed, off_stack, apart, DCTX_SIZEOF, WILDCOPY_OVERLENGTH, ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split, DCTX_entropy_rep, DCTX_litExtraBuffer in *.
  specialize (D3 NZ).
  assert (PL : DST <= LITP /\ LBE + 32 <= DST + CAP) by (clear - D5 EL; destruct D5 as [(E & _)|[(E & _)|(_ & A & B & _)]]; [lia | lia | lia]). subst OEND.
  clear D5 D4.
  repeat (split; [first [assumption | clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 G16 D3 PL N1 NZ T4 T5 T6; lia]|]).
  split; [clear - P2; lia|]. split; [clear - P3; lia|]. split; [clear - P4; lia|]. split; [clear - P1; lia|].
  split; [clear - T7; lia|]. split; [clear - T8; lia|]. split; [clear - T9; lia|].
  split; [clear - P6; lia|]. split; [clear - P5; lia|].
  split; [clear - T10; lia|]. split; [clear - T11; lia|]. split; [clear - T12; lia|].
  split; [clear - P5 PL G7 G8; lia|].
  split; [clear - T13; lia|]. split; [clear - T14; lia|]. split; [clear - T15; lia|]. split; [clear - P7; lia|].
  split; [lia|]. split; [left; clear - PL G7; lia|].
  split; [exact OKLL|]. split; [exact OKOF| exact OKML].
Qed.

(* [comment removed for export] *)
Lemma seql_static_m0 : forall P OEND,
  seql_ranges P -> seql_side P -> seql_sep P -> seql_tables P -> y_nbSeq P <> 0 -> 1 <= zlen (y_sq P) ->
  y_LOC P = 0 -> OEND = y_DST P + y_CAP P ->
  seql_static P OEND (y_LITP P) (y_LBE P) 0.
Proof.
  intros P OEND RG SD SEP TB NZ N1 EL EO.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_ranges seql_side seql_sep seql_tables y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in *.
  destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
  destruct SD as (D1 & D2 & D3 & D4 & D5).
  destruct SEP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  destruct TB as ((_ & OKLL) & (_ & OKOF) & (_ & OKML) & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15).
  unfold seq_lit_placed, off_stack, apart, DCTX_SIZEOF, WILDCOPY_OVERLENGTH, ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split, DCTX_entropy_rep, DCTX_litExtraBuffer in *.
  specialize (D3 NZ).
  assert (PL : LBE + 32 <= B0 \/ B1 <= LITP) by (clear - D5 EL; destruct D5 as [(_ & A)|[(E & _)|(E & _)]]; [lia | lia | lia]). specialize (P8 ltac:(clear - EL; lia)). subst OEND.
  clear D5 D4.
  repeat (split; [first [assumption | clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 G16 D3 PL N1 NZ T4 T5 T6; lia]|]).
  split; [clear - P2; lia|]. split; [clear - P3; lia|]. split; [clear - P4; lia|]. split; [clear - P1; lia|].
  split; [clear - T7; lia|]. split; [clear - T8; lia|]. split; [clear - T9; lia|].
  split; [clear - P6; lia|]. split; [clear - P5; lia|].
  split; [clear - T10; lia|]. split; [clear - T11; lia|]. split; [clear - T12; lia|].
  split; [clear - P8; lia|].
  split; [clear - T13; lia|]. split; [clear - T14; lia|]. split; [clear - T15; lia|]. split; [clear - P7; lia|].
  split; [lia|]. split; [right; clear - PL; lia|].
  split; [exact OKLL|]. split; [exact OKOF| exact OKML].
Qed.

(* [comment removed for export] *)
Lemma seql_static_m1 : forall P OEND,
  seql_ranges P -> seql_side P -> seql_sep P -> seql_tables P -> y_nbSeq P <> 0 -> 1 <= zlen (y_sq P) ->
  y_LOC P = 1 -> OEND = y_LITB P ->
  seql_static P OEND (y_LITP P) (y_LBE P) 1.
Proof.
  intros P OEND RG SD SEP TB NZ N1 EL EO.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_ranges seql_side seql_sep seql_tables y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in *.
  destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
  destruct SD as (D1 & D2 & D3 & D4 & D5).
  destruct SEP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  destruct TB as ((_ & OKLL) & (_ & OKOF) & (_ & OKML) & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15).
  unfold seq_lit_placed, off_stack, apart, DCTX_SIZEOF, WILDCOPY_OVERLENGTH, ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split, DCTX_entropy_rep, DCTX_litExtraBuffer in *.
  specialize (D3 NZ).
  assert (PL : DST <= LITB <= DST + CAP /\ LITB <= LITP /\ LBE + 32 <= B1) by (clear - D5 EL; destruct D5 as [(E & _)|[(_ & A)|(E & _)]]; [lia | lia | lia]). specialize (P8 ltac:(clear - EL; lia)). subst OEND.
  clear D5 D4.
  repeat (split; [first [assumption | clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 G16 D3 PL N1 NZ T4 T5 T6; lia]|]).
  split; [clear - P2; lia|]. split; [clear - P3; lia|]. split; [clear - P4; lia|]. split; [clear - P1; lia|].
  split; [clear - T7; lia|]. split; [clear - T8; lia|]. split; [clear - T9; lia|].
  split; [clear - P6; lia|]. split; [clear - P5; lia|].
  split; [clear - T10; lia|]. split; [clear - T11; lia|]. split; [clear - T12; lia|].
  split; [clear - P8; lia|].
  split; [clear - T13; lia|]. split; [clear - T14; lia|]. split; [clear - T15; lia|]. split; [clear - P7; lia|].
  split; [lia|]. split; [right; clear - PL G7; lia|].
  split; [exact OKLL|]. split; [exact OKOF| exact OKML].
Qed.

(* [comment removed for export] *)
Lemma seql_static_x : forall P OEND,
  seql_ranges P -> seql_side P -> seql_sep P -> seql_tables P -> y_nbSeq P <> 0 -> 1 <= zlen (y_sq P) ->
  y_DST P <= OEND <= y_DST P + y_CAP P ->
  seql_static P OEND (y_DCTX P + 30372) (y_DCTX P + 95908) 0.
Proof.
  intros P OEND RG SD SEP TB NZ N1 EO.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_ranges seql_side seql_sep seql_tables y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in *.
  destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
  destruct SD as (D1 & D2 & D3 & D4 & D5).
  destruct SEP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  destruct TB as ((_ & OKLL) & (_ & OKOF) & (_ & OKML) & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15).
  unfold seq_lit_placed, off_stack, apart, DCTX_SIZEOF, WILDCOPY_OVERLENGTH, ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split, DCTX_entropy_rep, DCTX_litExtraBuffer in *.
  specialize (D3 NZ).
  assert (PL : True) by exact I.
  clear D5 D4.
  repeat (split; [first [assumption | clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 G16 D3 PL N1 NZ T4 T5 T6 EO; lia]|]).
  split; [clear - P5; lia|].
  repeat (split; [first [assumption | clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 G16 D3 PL N1 NZ T4 T5 T6 EO; lia]|]).
  split; [clear - P2; lia|]. split; [clear - P3; lia|]. split; [clear - P1 G2; lia|]. split; [clear - P1; lia|].
  split; [clear - T7; lia|]. split; [clear - T8; lia|]. split; [clear - T9; lia|].
  split; [clear - P6; lia|]. split; [clear - P5; lia|].
  split; [clear - T10; lia|]. split; [clear - T11; lia|]. split; [clear - T12; lia|].
  split; [lia|].
  split; [clear - T13; lia|]. split; [clear - T14; lia|]. split; [clear - T15; lia|]. split; [clear - P7; lia|].
  split; [lia|]. split; [right; clear - P5; lia|].
  split; [exact OKLL|]. split; [exact OKOF| exact OKML].
Qed.

(* [comment removed for export] *)
Lemma seql_prologue_frame : forall (m : fmem) A j (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word),
  rw_cells psegs m A (CB 504 j :: [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) ->
  exists w_c0 w_c8 w_c16 w_c24 w_c32 w_c40 w_c48 w_c56 w_c64 w_c72 w_c80 w_c88 w_c96 w_c104 w_c112 w_c120 w_c128 w_c136 w_c144 w_c152 w_c160 w_c168 w_c176 w_c184 w_c192 w_c200 w_c208 w_c216 w_c224 w_c232 w_c240 w_c248 w_c256 w_c264 w_c272 w_c472 jpad jseq rl rm ro,
    rw_cells psegs m A [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C8 w_c96; C8 w_c104; C8 w_c112; C8 w_c120; C8 w_c128; C8 w_c136; C8 w_c144; C8 w_c152; C8 w_c160; C8 w_c168; C4 w_c176; CB 4 jpad; C8 w_c184; C8 w_c192; C8 w_c200; C8 w_c208; C8 w_c216; C8 w_c224; C8 w_c232; C8 w_c240; C8 w_c248; C8 w_c256; C8 w_c264; C8 w_c272; CB 192 (seql_ring_bytes rl rm ro); C8 w_c472; CB 24 jseq; CB 104 (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++ le8 s1 ++ le8 s0 ++ le8 ra)].
Proof.
  intros m A j s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra FR.
  change (rw_cells psegs m A ([CB 504 j] ++ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ++ [])) in FR.
  apply rw_cells_merge in FR. cbn [cells_size csize Nat.add cells_bytes cbytes] in FR. rewrite !app_nil_r in FR.
  change (rw_cells psegs m A ([] ++ CB 504 j :: [CB 104 (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++ le8 s1 ++ le8 s0 ++ le8 ra)])) in FR.
  apply (rw_cells_split_CB psegs m A [] 504 j _ [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 4; 4; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 192; 8; 24]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app] in FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [] _ _ FR) as (w_c0 & FR0) end; cbn [app] in FR0; clear FR; rename FR0 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0] _ _ FR) as (w_c8 & FR1) end; cbn [app] in FR1; clear FR; rename FR1 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8] _ _ FR) as (w_c16 & FR2) end; cbn [app] in FR2; clear FR; rename FR2 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16] _ _ FR) as (w_c24 & FR3) end; cbn [app] in FR3; clear FR; rename FR3 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24] _ _ FR) as (w_c32 & FR4) end; cbn [app] in FR4; clear FR; rename FR4 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32] _ _ FR) as (w_c40 & FR5) end; cbn [app] in FR5; clear FR; rename FR5 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40] _ _ FR) as (w_c48 & FR6) end; cbn [app] in FR6; clear FR; rename FR6 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48] _ _ FR) as (w_c56 & FR7) end; cbn [app] in FR7; clear FR; rename FR7 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56] _ _ FR) as (w_c64 & FR8) end; cbn [app] in FR8; clear FR; rename FR8 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64] _ _ FR) as (w_c72 & FR9) end; cbn [app] in FR9; clear FR; rename FR9 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72] _ _ FR) as (w_c80 & FR10) end; cbn [app] in FR10; clear FR; rename FR10 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80] _ _ FR) as (w_c88 & FR11) end; cbn [app] in FR11; clear FR; rename FR11 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88] _ _ FR) as (w_c96 & FR12) end; cbn [app] in FR12; clear FR; rename FR12 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C8 w_c96] _ _ FR) as (w_c104 & FR13) end; cbn [app] in FR13; clear FR; rename FR13 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C8 w_c96; C8 w_c104] _ _ FR) as (w_c112 & FR14) end; cbn [app] in FR14; clear FR; rename FR14 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C8 w_c96; C8 w_c104; C8 w_c112] _ _ FR) as (w_c120 & FR15) end; cbn [app] in FR15; clear FR; rename FR15 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C8 w_c96; C8 w_c104; C8 w_c112; C8 w_c120] _ _ FR) as (w_c128 & FR16) end; cbn [app] in FR16; clear FR; rename FR16 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C8 w_c96; C8 w_c104; C8 w_c112; C8 w_c120; C8 w_c128] _ _ FR) as (w_c136 & FR17) end; cbn [app] in FR17; clear FR; rename FR17 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C8 w_c96; C8 w_c104; C8 w_c112; C8 w_c120; C8 w_c128; C8 w_c136] _ _ FR) as (w_c144 & FR18) end; cbn [app] in FR18; clear FR; rename FR18 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C8 w_c96; C8 w_c104; C8 w_c112; C8 w_c120; C8 w_c128; C8 w_c136; C8 w_c144] _ _ FR) as (w_c152 & FR19) end; cbn [app] in FR19; clear FR; rename FR19 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C8 w_c96; C8 w_c104; C8 w_c112; C8 w_c120; C8 w_c128; C8 w_c136; C8 w_c144; C8 w_c152] _ _ FR) as (w_c160 & FR20) end; cbn [app] in FR20; clear FR; rename FR20 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C8 w_c96; C8 w_c104; C8 w_c112; C8 w_c120; C8 w_c128; C8 w_c136; C8 w_c144; C8 w_c152; C8 w_c160] _ _ FR) as (w_c168 & FR21) end; cbn [app] in FR21; clear FR; rename FR21 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb4_as_c4 mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C8 w_c96; C8 w_c104; C8 w_c112; C8 w_c120; C8 w_c128; C8 w_c136; C8 w_c144; C8 w_c152; C8 w_c160; C8 w_c168] _ _ FR) as (w_c176 & FR22) end; cbn [app] in FR22; clear FR; rename FR22 into FR.
  lazymatch type of FR with rw_cells _ _ _ ?cs => lazymatch cs with context [CB 4 ?jp :: CB 8 _ :: _] => set (jpad := jp) in FR; clearbody jpad end end.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C8 w_c96; C8 w_c104; C8 w_c112; C8 w_c120; C8 w_c128; C8 w_c136; C8 w_c144; C8 w_c152; C8 w_c160; C8 w_c168; C4 w_c176; CB 4 jpad] _ _ FR) as (w_c184 & FR23) end; cbn [app] in FR23; clear FR; rename FR23 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C8 w_c96; C8 w_c104; C8 w_c112; C8 w_c120; C8 w_c128; C8 w_c136; C8 w_c144; C8 w_c152; C8 w_c160; C8 w_c168; C4 w_c176; CB 4 jpad; C8 w_c184] _ _ FR) as (w_c192 & FR24) end; cbn [app] in FR24; clear FR; rename FR24 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C8 w_c96; C8 w_c104; C8 w_c112; C8 w_c120; C8 w_c128; C8 w_c136; C8 w_c144; C8 w_c152; C8 w_c160; C8 w_c168; C4 w_c176; CB 4 jpad; C8 w_c184; C8 w_c192] _ _ FR) as (w_c200 & FR25) end; cbn [app] in FR25; clear FR; rename FR25 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C8 w_c96; C8 w_c104; C8 w_c112; C8 w_c120; C8 w_c128; C8 w_c136; C8 w_c144; C8 w_c152; C8 w_c160; C8 w_c168; C4 w_c176; CB 4 jpad; C8 w_c184; C8 w_c192; C8 w_c200] _ _ FR) as (w_c208 & FR26) end; cbn [app] in FR26; clear FR; rename FR26 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C8 w_c96; C8 w_c104; C8 w_c112; C8 w_c120; C8 w_c128; C8 w_c136; C8 w_c144; C8 w_c152; C8 w_c160; C8 w_c168; C4 w_c176; CB 4 jpad; C8 w_c184; C8 w_c192; C8 w_c200; C8 w_c208] _ _ FR) as (w_c216 & FR27) end; cbn [app] in FR27; clear FR; rename FR27 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C8 w_c96; C8 w_c104; C8 w_c112; C8 w_c120; C8 w_c128; C8 w_c136; C8 w_c144; C8 w_c152; C8 w_c160; C8 w_c168; C4 w_c176; CB 4 jpad; C8 w_c184; C8 w_c192; C8 w_c200; C8 w_c208; C8 w_c216] _ _ FR) as (w_c224 & FR28) end; cbn [app] in FR28; clear FR; rename FR28 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C8 w_c96; C8 w_c104; C8 w_c112; C8 w_c120; C8 w_c128; C8 w_c136; C8 w_c144; C8 w_c152; C8 w_c160; C8 w_c168; C4 w_c176; CB 4 jpad; C8 w_c184; C8 w_c192; C8 w_c200; C8 w_c208; C8 w_c216; C8 w_c224] _ _ FR) as (w_c232 & FR29) end; cbn [app] in FR29; clear FR; rename FR29 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C8 w_c96; C8 w_c104; C8 w_c112; C8 w_c120; C8 w_c128; C8 w_c136; C8 w_c144; C8 w_c152; C8 w_c160; C8 w_c168; C4 w_c176; CB 4 jpad; C8 w_c184; C8 w_c192; C8 w_c200; C8 w_c208; C8 w_c216; C8 w_c224; C8 w_c232] _ _ FR) as (w_c240 & FR30) end; cbn [app] in FR30; clear FR; rename FR30 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C8 w_c96; C8 w_c104; C8 w_c112; C8 w_c120; C8 w_c128; C8 w_c136; C8 w_c144; C8 w_c152; C8 w_c160; C8 w_c168; C4 w_c176; CB 4 jpad; C8 w_c184; C8 w_c192; C8 w_c200; C8 w_c208; C8 w_c216; C8 w_c224; C8 w_c232; C8 w_c240] _ _ FR) as (w_c248 & FR31) end; cbn [app] in FR31; clear FR; rename FR31 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C8 w_c96; C8 w_c104; C8 w_c112; C8 w_c120; C8 w_c128; C8 w_c136; C8 w_c144; C8 w_c152; C8 w_c160; C8 w_c168; C4 w_c176; CB 4 jpad; C8 w_c184; C8 w_c192; C8 w_c200; C8 w_c208; C8 w_c216; C8 w_c224; C8 w_c232; C8 w_c240; C8 w_c248] _ _ FR) as (w_c256 & FR32) end; cbn [app] in FR32; clear FR; rename FR32 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C8 w_c96; C8 w_c104; C8 w_c112; C8 w_c120; C8 w_c128; C8 w_c136; C8 w_c144; C8 w_c152; C8 w_c160; C8 w_c168; C4 w_c176; CB 4 jpad; C8 w_c184; C8 w_c192; C8 w_c200; C8 w_c208; C8 w_c216; C8 w_c224; C8 w_c232; C8 w_c240; C8 w_c248; C8 w_c256] _ _ FR) as (w_c264 & FR33) end; cbn [app] in FR33; clear FR; rename FR33 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C8 w_c96; C8 w_c104; C8 w_c112; C8 w_c120; C8 w_c128; C8 w_c136; C8 w_c144; C8 w_c152; C8 w_c160; C8 w_c168; C4 w_c176; CB 4 jpad; C8 w_c184; C8 w_c192; C8 w_c200; C8 w_c208; C8 w_c216; C8 w_c224; C8 w_c232; C8 w_c240; C8 w_c248; C8 w_c256; C8 w_c264] _ _ FR) as (w_c272 & FR34) end; cbn [app] in FR34; clear FR; rename FR34 into FR.
  lazymatch type of FR with rw_cells _ _ _ ?cs => lazymatch cs with context [CB 192 ?jr :: _] => let HL := fresh "HL" in assert (HL : length jr = 192%nat) by (pose proof FR as [[WF _] _]; repeat (apply cells_wf_app in WF || (cbn [cells_wf cell_wf app] in WF)); clear - WF; repeat match type of WF with _ /\ _ => let W := fresh in destruct WF as (W & WF) end; assumption); destruct (seql_ring_any jr HL) as (rl & rm & ro & ERING); rewrite <- ERING in FR; clear ERING HL end end.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 psegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C8 w_c96; C8 w_c104; C8 w_c112; C8 w_c120; C8 w_c128; C8 w_c136; C8 w_c144; C8 w_c152; C8 w_c160; C8 w_c168; C4 w_c176; CB 4 jpad; C8 w_c184; C8 w_c192; C8 w_c200; C8 w_c208; C8 w_c216; C8 w_c224; C8 w_c232; C8 w_c240; C8 w_c248; C8 w_c256; C8 w_c264; C8 w_c272; CB 192 (seql_ring_bytes rl rm ro)] _ _ FR) as (w_c472 & FR35) end; cbn [app] in FR35; clear FR; rename FR35 into FR.
  lazymatch type of FR with rw_cells _ _ _ ?cs => lazymatch cs with context [CB 24 ?js :: _] => set (jseq := js) in FR; clearbody jseq end end.
  do 41 eexists. exact FR.
Qed.
