(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost StrFun ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_lbase RZ_seq_s_lkit RZ_seq_s_ibase.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma cb4_as_c4 : forall (m : fmem) A pre j post,
  rw_cells usegs m A (pre ++ CB 4 j :: post) -> exists w, rw_cells usegs m A (pre ++ C4 w :: post).
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

Lemma seqs_static_intro1 : forall P OEND,
  seqs_ranges P -> seqs_side P -> seqs_sep P -> seqs_tables P -> v_nbSeq P <> 0 -> 1 <= zlen (v_sq P) ->
  v_LOC P = 2 -> OEND = v_DST P + v_CAP P ->
  seqs_static P OEND (v_LITP P) (v_LBE P) 2.
Proof.
  intros P OEND RG SD SEP TB NZ N1 EL EO.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_static seqs_ranges seqs_side seqs_sep seqs_tables v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in *.
  destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
  destruct SD as (D1 & D2 & D3 & D4 & D5).
  destruct SEP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  destruct TB as ((_ & OKLL) & (_ & OKOF) & (_ & OKML) & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & AL).
  unfold seq_lit_placed, off_stack, apart, DCTX_SIZEOF, WILDCOPY_OVERLENGTH, ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split, DCTX_entropy_rep in *.
  specialize (D3 NZ). subst OEND.
  assert (PL : DST <= LITP /\ LBE + 32 <= DST + CAP) by (clear - D5 EL; destruct D5 as [(E & _)|[(E & _)|(_ & A & B & _)]]; [lia | lia | lia]).
  clear D5 D4.
  repeat (split; [first [assumption | clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 G16 D3 PL N1 NZ T4 T5 T6; lia]|]).
  split; [clear - P2; lia|]. split; [clear - P3; lia|]. split; [clear - P4; lia|]. split; [clear - P1; lia|].
  split; [clear - T7; lia|]. split; [clear - T8; lia|]. split; [clear - T9; lia|].
  split; [clear - P6; lia|]. split; [clear - P5; lia|].
  split; [clear - T10; lia|]. split; [clear - T11; lia|]. split; [clear - T12; lia|].
  split; [clear - P5 PL G7 G8; lia|].
  split; [clear - T13; lia|]. split; [clear - T14; lia|]. split; [clear - T15; lia|]. split; [clear - P7; lia|].
  split; [lia|]. split; [left; clear - PL G7; lia|].
  split; [exact AL|]. split; [exact OKLL|]. split; [exact OKOF| exact OKML].
Qed.

Lemma seqs_static_intro2 : forall P OEND,
  seqs_ranges P -> seqs_side P -> seqs_sep P -> seqs_tables P -> v_nbSeq P <> 0 -> 1 <= zlen (v_sq P) ->
  v_DST P <= OEND <= v_DST P + v_CAP P ->
  seqs_static P OEND (v_DCTX P + 30372) (v_DCTX P + 95908) 0.
Proof.
  intros P OEND RG SD SEP TB NZ N1 EO.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_static seqs_ranges seqs_side seqs_sep seqs_tables v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in *.
  destruct RG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
  destruct SD as (D1 & D2 & D3 & D4 & D5).
  destruct SEP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  destruct TB as ((_ & OKLL) & (_ & OKOF) & (_ & OKML) & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & AL).
  unfold off_stack, apart, DCTX_SIZEOF, WILDCOPY_OVERLENGTH, DCTX_entropy_rep in *.
  specialize (D3 NZ). clear D5 D4.
  repeat (split; [first [assumption | clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 G16 D3 N1 NZ T4 T5 T6 EO; lia]|]).
  split; [clear - P5; lia|].
  repeat (split; [first [assumption | clear - G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 G16 D3 N1 NZ T4 T5 T6 EO; lia]|]).
  split; [clear - P2; lia|]. split; [clear - P3; lia|]. split; [clear - P1 G2; lia|]. split; [clear - P1; lia|].
  split; [clear - T7; lia|]. split; [clear - T8; lia|]. split; [clear - T9; lia|].
  split; [clear - P6; lia|]. split; [clear - P5; lia|].
  split; [clear - T10; lia|]. split; [clear - T11; lia|]. split; [clear - T12; lia|].
  split; [lia|].
  split; [clear - T13; lia|]. split; [clear - T14; lia|]. split; [clear - T15; lia|]. split; [clear - P7; lia|].
  split; [lia|]. split; [right; clear - P5; lia|].
  split; [exact AL|]. split; [exact OKLL|]. split; [exact OKOF| exact OKML].
Qed.

(* [comment removed for export] *)
Lemma seqs_prologue_frame : forall (m : fmem) A j (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word),
  rw_cells usegs m A (CB 232 j :: [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) ->
  exists w_c0 w_c8 w_c16 w_c24 w_c32 w_c40 w_c48 w_c56 w_c64 w_c72 w_c80 w_c88 w_c96 w_c104 w_c112 w_c120 w_c128 w_c136 w_c144 w_c152 w_c160 w_c168 w_c176 w_c184 w_c192 w_c200 jpad jseq,
    rw_cells usegs m A [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C4 w_c96; CB 4 jpad; C8 w_c104; C8 w_c112; C8 w_c120; C8 w_c128; C8 w_c136; C8 w_c144; C8 w_c152; C8 w_c160; C8 w_c168; C8 w_c176; C8 w_c184; C8 w_c192; C8 w_c200; CB 24 jseq; CB 104 (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++ le8 s1 ++ le8 s0 ++ le8 ra)].
Proof.
  intros m A j s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra FR.
  change (rw_cells usegs m A ([CB 232 j] ++ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ++ [])) in FR.
  apply rw_cells_merge in FR. cbn [cells_size csize Nat.add cells_bytes cbytes] in FR. rewrite !app_nil_r in FR.
  change (rw_cells usegs m A ([] ++ CB 232 j :: [CB 104 (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++ le8 s1 ++ le8 s0 ++ le8 ra)])) in FR.
  apply (rw_cells_split_CB usegs m A [] 232 j _ [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 4; 4; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 24]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app] in FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 usegs mm AA [] _ _ FR) as (w_c0 & FR0) end; cbn [app] in FR0; clear FR; rename FR0 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 usegs mm AA [C8 w_c0] _ _ FR) as (w_c8 & FR1) end; cbn [app] in FR1; clear FR; rename FR1 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 usegs mm AA [C8 w_c0; C8 w_c8] _ _ FR) as (w_c16 & FR2) end; cbn [app] in FR2; clear FR; rename FR2 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 usegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16] _ _ FR) as (w_c24 & FR3) end; cbn [app] in FR3; clear FR; rename FR3 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 usegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24] _ _ FR) as (w_c32 & FR4) end; cbn [app] in FR4; clear FR; rename FR4 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 usegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32] _ _ FR) as (w_c40 & FR5) end; cbn [app] in FR5; clear FR; rename FR5 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 usegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40] _ _ FR) as (w_c48 & FR6) end; cbn [app] in FR6; clear FR; rename FR6 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 usegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48] _ _ FR) as (w_c56 & FR7) end; cbn [app] in FR7; clear FR; rename FR7 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 usegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56] _ _ FR) as (w_c64 & FR8) end; cbn [app] in FR8; clear FR; rename FR8 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 usegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64] _ _ FR) as (w_c72 & FR9) end; cbn [app] in FR9; clear FR; rename FR9 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 usegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72] _ _ FR) as (w_c80 & FR10) end; cbn [app] in FR10; clear FR; rename FR10 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 usegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80] _ _ FR) as (w_c88 & FR11) end; cbn [app] in FR11; clear FR; rename FR11 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb4_as_c4 mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88] _ _ FR) as (w_c96 & FR12) end; cbn [app] in FR12; clear FR; rename FR12 into FR.
  lazymatch type of FR with rw_cells _ _ _ ?cs => lazymatch cs with context [CB 4 ?jp :: CB 8 _ :: _] => set (jpad := jp) in FR; clearbody jpad end end.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 usegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C4 w_c96; CB 4 jpad] _ _ FR) as (w_c104 & FR13) end; cbn [app] in FR13; clear FR; rename FR13 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 usegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C4 w_c96; CB 4 jpad; C8 w_c104] _ _ FR) as (w_c112 & FR14) end; cbn [app] in FR14; clear FR; rename FR14 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 usegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C4 w_c96; CB 4 jpad; C8 w_c104; C8 w_c112] _ _ FR) as (w_c120 & FR15) end; cbn [app] in FR15; clear FR; rename FR15 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 usegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C4 w_c96; CB 4 jpad; C8 w_c104; C8 w_c112; C8 w_c120] _ _ FR) as (w_c128 & FR16) end; cbn [app] in FR16; clear FR; rename FR16 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 usegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C4 w_c96; CB 4 jpad; C8 w_c104; C8 w_c112; C8 w_c120; C8 w_c128] _ _ FR) as (w_c136 & FR17) end; cbn [app] in FR17; clear FR; rename FR17 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 usegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C4 w_c96; CB 4 jpad; C8 w_c104; C8 w_c112; C8 w_c120; C8 w_c128; C8 w_c136] _ _ FR) as (w_c144 & FR18) end; cbn [app] in FR18; clear FR; rename FR18 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 usegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C4 w_c96; CB 4 jpad; C8 w_c104; C8 w_c112; C8 w_c120; C8 w_c128; C8 w_c136; C8 w_c144] _ _ FR) as (w_c152 & FR19) end; cbn [app] in FR19; clear FR; rename FR19 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 usegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C4 w_c96; CB 4 jpad; C8 w_c104; C8 w_c112; C8 w_c120; C8 w_c128; C8 w_c136; C8 w_c144; C8 w_c152] _ _ FR) as (w_c160 & FR20) end; cbn [app] in FR20; clear FR; rename FR20 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 usegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C4 w_c96; CB 4 jpad; C8 w_c104; C8 w_c112; C8 w_c120; C8 w_c128; C8 w_c136; C8 w_c144; C8 w_c152; C8 w_c160] _ _ FR) as (w_c168 & FR21) end; cbn [app] in FR21; clear FR; rename FR21 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 usegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C4 w_c96; CB 4 jpad; C8 w_c104; C8 w_c112; C8 w_c120; C8 w_c128; C8 w_c136; C8 w_c144; C8 w_c152; C8 w_c160; C8 w_c168] _ _ FR) as (w_c176 & FR22) end; cbn [app] in FR22; clear FR; rename FR22 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 usegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C4 w_c96; CB 4 jpad; C8 w_c104; C8 w_c112; C8 w_c120; C8 w_c128; C8 w_c136; C8 w_c144; C8 w_c152; C8 w_c160; C8 w_c168; C8 w_c176] _ _ FR) as (w_c184 & FR23) end; cbn [app] in FR23; clear FR; rename FR23 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 usegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C4 w_c96; CB 4 jpad; C8 w_c104; C8 w_c112; C8 w_c120; C8 w_c128; C8 w_c136; C8 w_c144; C8 w_c152; C8 w_c160; C8 w_c168; C8 w_c176; C8 w_c184] _ _ FR) as (w_c192 & FR24) end; cbn [app] in FR24; clear FR; rename FR24 into FR.
  lazymatch type of FR with rw_cells _ ?mm ?AA _ => destruct (cb8_as_c8 usegs mm AA [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 w_c80; C8 w_c88; C4 w_c96; CB 4 jpad; C8 w_c104; C8 w_c112; C8 w_c120; C8 w_c128; C8 w_c136; C8 w_c144; C8 w_c152; C8 w_c160; C8 w_c168; C8 w_c176; C8 w_c184; C8 w_c192] _ _ FR) as (w_c200 & FR25) end; cbn [app] in FR25; clear FR; rename FR25 into FR.
  do 28 eexists. exact FR.
Qed.

Ltac seqs_cb8_pre cs :=
  lazymatch cs with
  | CB 8 _ :: _ => constr:(@nil cell)
  | ?c :: ?rest => let p := seqs_cb8_pre rest in constr:(c :: p)
  end.

Lemma seqs_prologue_frame384 : forall (m : fmem) A j (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word),
  rw_cells usegs m A (CB 280 j :: [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) ->
  exists c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 jbd u176 u184 u192 u200 u208 u216 c224 c232 c240 c248 jseq,
    rw_cells usegs m A [C8 c0; C8 c8; C8 c16; C8 c24; C8 c32; C8 c40; C8 c48; C8 c56; C8 c64; C8 c72; C8 c80; C8 c88; C8 c96; C8 c104; C8 c112; C8 c120; C8 c128; CB 40 jbd; C8 u176; C8 u184; C8 u192; C8 u200; C8 u208; C8 u216; C8 c224; C8 c232; C8 c240; C8 c248; CB 24 jseq; CB 104 (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++ le8 s1 ++ le8 s0 ++ le8 ra)].
Proof.
  intros m A j s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra FR.
  change (rw_cells usegs m A ([CB 280 j] ++ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ++ [])) in FR.
  apply rw_cells_merge in FR. cbn [cells_size csize Nat.add cells_bytes cbytes] in FR. rewrite !app_nil_r in FR.
  change (rw_cells usegs m A ([] ++ CB 280 j :: [CB 104 (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++ le8 s1 ++ le8 s0 ++ le8 ra)])) in FR.
  apply (rw_cells_split_CB usegs m A [] 280 j _ [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 40; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 24]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat lazymatch type of FR with rw_cells _ ?mm ?AA ?cs =>
    let pre := seqs_cb8_pre cs in
    let w := fresh "w" in let FR' := fresh "FR" in
    destruct (cb8_as_c8 usegs mm AA pre _ _ FR) as (w & FR'); cbn [app] in FR'; clear FR; rename FR' into FR end.
  do 29 eexists. exact FR.
Qed.
