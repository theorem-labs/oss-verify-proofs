(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
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
  intros m A j s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra Frame.
  lazymatch type of Frame with
  | rw_cells _ _ _ (?locals :: ?saved) => pose proof (rw_cells_merge usegs m A [locals] saved [] Frame) as Folded
  end.
  cbn [app cells_size csize cells_bytes cbytes Nat.add] in Folded. rewrite app_nil_r in Folded.
  pose proof (rw_cells_split_CB usegs m A [] 232 j _ (repeat 8 12 ++ [4; 4] ++ repeat 8 13 ++ [24])%nat Folded eq_refl) as Carved.
  cbn [app repeat mk_CB_cells] in Carved. clear Folded Frame.
  let rec lead n cs :=
    lazymatch cs with
    | CB n _ :: _ => constr:(@nil cell)
    | ?c :: ?rest => let p := lead n rest in constr:(c :: p)
    end in
  lazymatch type of Carved with
  | rw_cells _ _ _ ?cs => let p := lead 4%nat cs in apply (cb4_as_c4 m A p) in Carved
  end;
  destruct Carved as [w96 Carved]; cbn [app] in Carved;
  repeat lazymatch type of Carved with
    | rw_cells _ _ _ ?cs =>
        let p := lead 8%nat cs in
        apply (cb8_as_c8 usegs m A p) in Carved; destruct Carved as [? Carved]; cbn [app] in Carved
    end.
  do 28 eexists. exact Carved.
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
  intros m A j s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra Frame.
  lazymatch type of Frame with
  | rw_cells _ _ _ (?locals :: ?saved) => pose proof (rw_cells_merge usegs m A [locals] saved [] Frame) as Folded
  end.
  cbn [app cells_size csize cells_bytes cbytes Nat.add] in Folded. rewrite app_nil_r in Folded.
  pose proof (rw_cells_split_CB usegs m A [] 280 j _ (repeat 8 17 ++ [40] ++ repeat 8 10 ++ [24])%nat Folded eq_refl) as Carved.
  cbn [app repeat mk_CB_cells] in Carved. clear Folded Frame.
  repeat lazymatch type of Carved with
    | rw_cells _ _ _ ?cs =>
        let p := seqs_cb8_pre cs in
        apply (cb8_as_c8 usegs m A p) in Carved; destruct Carved as [? Carved]; cbn [app] in Carved
    end.
  do 29 eexists. exact Carved.
Qed.
