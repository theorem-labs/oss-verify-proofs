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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_ibase.
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
  evt usegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19' x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc None m (seg_rom usegs)) ->
  evt usegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc None m (seg_rom usegs)).
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
  destruct TB as ((_ & OKLL) & (_ & OKOF) & (_ & OKML) & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16).
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
  split; [exact T16|]. split; [exact OKLL|]. split; [exact OKOF| exact OKML].
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
  destruct TB as ((_ & OKLL) & (_ & OKOF) & (_ & OKML) & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16).
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
  split; [exact T16|]. split; [exact OKLL|]. split; [exact OKOF| exact OKML].
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
  destruct TB as ((_ & OKLL) & (_ & OKOF) & (_ & OKML) & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16).
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
  split; [exact T16|]. split; [exact OKLL|]. split; [exact OKOF| exact OKML].
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
  destruct TB as ((_ & OKLL) & (_ & OKOF) & (_ & OKML) & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16).
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
  split; [exact T16|]. split; [exact OKLL|]. split; [exact OKOF| exact OKML].
Qed.

(* [comment removed for export] *)
Ltac seql_cb8_pre cs :=
  lazymatch cs with
  | CB 8 _ :: _ => constr:(@nil cell)
  | ?c :: ?rest => let p := seql_cb8_pre rest in constr:(c :: p)
  end.

Lemma seql_prologue_frame : forall (m : fmem) A j (sv : list cell),
  rw_cells usegs m A (CB 584 j :: sv) ->
  exists c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c144 c152 c160 c168 c176 c184 c192 c200 c208 c216 c224 c232 c240 jbd u288 u296 u304 u312 u320 u328 c336 c344 c352 jring c552 jseq,
    rw_cells usegs m A ([C8 c0; C8 c8; C8 c16; C8 c24; C8 c32; C8 c40; C8 c48; C8 c56; C8 c64; C8 c72; C8 c80; C8 c88; C8 c96; C8 c104; C8 c112; C8 c120; C8 c128; C8 c136; C8 c144; C8 c152; C8 c160; C8 c168; C8 c176; C8 c184; C8 c192; C8 c200; C8 c208; C8 c216; C8 c224; C8 c232; C8 c240; CB 40 jbd; C8 u288; C8 u296; C8 u304; C8 u312; C8 u320; C8 u328; C8 c336; C8 c344; C8 c352; CB 192 jring; C8 c552; CB 24 jseq] ++ sv).
Proof.
  intros m A j sv FR.
  change (rw_cells usegs m A ([] ++ CB 584 j :: sv)) in FR.
  apply (rw_cells_split_CB usegs m A [] 584 j sv [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 40; 8; 8; 8; 8; 8; 8; 8; 8; 8; 192; 8; 24]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat lazymatch type of FR with rw_cells _ ?mm ?AA ?cs =>
    let pre := seql_cb8_pre cs in
    let w := fresh "w" in let FR' := fresh "FR" in
    destruct (cb8_as_c8 usegs mm AA pre _ _ FR) as (w & FR'); cbn [app] in FR'; clear FR; rename FR' into FR end.
  do 44 eexists. exact FR.
Qed.
