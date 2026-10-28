(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_lbase RZ_seq_s_lkit RZ_seq_s_ibase RZ_seq_s_iexit RZ_seq_s_ient seqS_kit_al seqD_kit_bitinit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seqs_entry : forall (P : ssp) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word),
  seqs_mem P -> seqs_ranges P -> seqs_side P -> seqs_sep P -> seqs_tables P -> v_nbSeq P <> 0 -> v_LOC P = 2 ->
  (forall OEND, seqs_static P OEND (v_LITP P) (v_LBE P) 2 -> ai_i0 P OEND (v_LITP P) (v_LBE P) 2) ->
  evt usegs (seqs_post P)
    (MS (mkR (v_ra P) (Z_to_bv 64 (v_SPV P)) (v_gp P) (v_tp P) t0 t1 t2 (v_s0 P) (v_s1 P) (Z_to_bv 64 (v_DCTX P)) (Z_to_bv 64 (v_DST P))
             (Z_to_bv 64 (v_CAP P)) (Z_to_bv 64 (v_SEQ P)) (Z_to_bv 64 (zlen (v_sq P))) (Z_to_bv 64 (v_nbSeq P)) a6 a7
             (v_s2 P) (v_s3 P) (v_s4 P) (v_s5 P) (v_s6 P) (v_s7 P) (v_s8 P) (v_s9 P) (v_s10 P) (v_s11 P) t3 t4 t5 t6)
        (v_F P) (Z_to_bv 64 0x1ac08) (v_fc P) None (v_m P) (seg_rom usegs)).
Proof.
  intros P t0 t1 t2 a6 a7 t3 t4 t5 t6 MEM RG SIDE SEP TBL NZ LV CONT.
  pose proof (seqs_static_intro1 P) as SINTRO.
  pose proof RG as RG0. pose proof SIDE as SIDE0. pose proof SEP as SEP0. pose proof TBL as TBL0.
  assert (FE1 : seqs_fe P = Z_to_bv 64 1) by (unfold seqs_fe; destruct (Z.eqb_spec (v_nbSeq P) 0); [contradiction|reflexivity]).
  unfold ai_i0, seqs_ifr in CONT.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_mem seqs_ranges seqs_side seqs_sep seqs_tables seqs_post seqs_saved v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in MEM, RG, SIDE, SEP, TBL, NZ, LV |- *.
  cbn [app seqs_post v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in CONT.
  destruct MEM as ((PT & REP & HH1 & HH3 & HH5) & (L1 & L2 & L3 & L4) & SQB & BUF & LRD & STK & MI).
  destruct (h5_view2 m DCTX ws HH5) as (H5O & H5L). pose proof H5O as H5V. unfold h5_vcells in H5V, H5O. rewrite L4, LV in H5O. rewrite L1, L2, L3, L4 in H5V. clear HH5 L1 L2 L3 L4.
  destruct TBL as ((TLL & _) & (TOF & _) & (TML & _) & TR).
  unfold dctx_ptrs, dctx_h1, dctx_h3 in *.
  unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation in *.
  assert (LSQ : Z.of_nat (length (map (Z_to_bv 8) sq)) = zlen sq) by (rewrite length_map; reflexivity).
  assert (PL : DST <= LITP /\ LBE + 32 <= DST + CAP /\ rdbl usegs m (DCTX + 30372) (DCTX + 95940)).
  { destruct SIDE as (_ & _ & _ & _ & D5). unfold seq_lit_placed, ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split, WILDCOPY_OVERLENGTH, DCTX_litExtraBuffer, DCTX_litExtraBuffer_sz in D5.
    destruct D5 as [(E & _)|[(E & _)|(_ & A & B & C)]]; [lia | lia |]. split; [exact A|]. split; [exact B|]. replace (DCTX + 95940) with (DCTX + 30372 + 65568) by lia. exact C. }
  destruct PL as (PL1 & PL2 & XLIT).
  assert (DAL : DCTX mod 8 = 0) by (destruct SIDE as (D1 & _); exact D1).
  assert (RA : 592 <= SPV < 2^47 /\ 4096 <= lo <= SPV - 592 /\ 4096 <= DCTX /\ DCTX + 95992 < 2^47 /\ 4096 <= DST < 2^47 /\ 32 <= CAP < 2^47 /\ 4096 <= DST + CAP < 2^47 /\
               4096 <= LITP < 2^47 /\ 4096 <= LBE < 2^47 /\ 1 <= nbSeq <= 98047 /\ 0 <= zlen sq < 2^47 /\ 4096 <= SEQ < 2^47)
    by (unfold DCTX_SIZEOF, WILDCOPY_OVERLENGTH in RG; lia).
  destruct TR as (_ & _ & _ & T7 & T8 & T9 & _ & _ & _ & T13 & T14 & T15 & _). destruct SEP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  unfold off_stack, apart, DCTX_SIZEOF, WILDCOPY_OVERLENGTH, DCTX_litExtraBuffer in P1, P2, P3, P4, P5, P6, P7, T7, T8, T9, T13, T14, T15.
  assert (X1 : SPV <= DCTX \/ DCTX + 95992 <= lo) by (clear - P1 RA; lia).
  assert (X2 : SPV <= B0 \/ B1 <= SPV - 384) by (clear - P2 RA; lia).
  assert (X3 : SPV <= LITP \/ LBE + 32 <= SPV - 384) by (clear - P4 RA; lia).
  assert (X4 : SPV <= SEQ \/ SEQ + zlen sq <= SPV - 384) by (clear - P3 RA; lia).
  assert (X5 : SPV <= LLT \/ LLT + 4104 <= SPV - 384) by (clear - T7 RA; lia).
  assert (X6 : SPV <= OFT \/ OFT + 2056 <= SPV - 384) by (clear - T8 RA; lia).
  assert (X7 : SPV <= MLT \/ MLT + 4104 <= SPV - 384) by (clear - T9 RA; lia).
  assert (X8 : B1 <= DCTX \/ DCTX + 95992 <= B0) by (clear - P5; lia).
  assert (X9 : SEQ + zlen sq <= DCTX + 26684 \/ DCTX + 95992 <= SEQ) by (clear - P7; lia).
  assert (X10 : LBE + 32 <= DCTX + 26684 \/ DCTX + 95992 <= LITP) by (clear - P5 PL1 PL2 RG; lia).
  assert (X11 : LLT + 4104 <= DCTX + 26684 \/ DCTX + 95992 <= LLT) by (clear - T13; lia).
  assert (X12 : OFT + 2056 <= DCTX + 26684 \/ DCTX + 95992 <= OFT) by (clear - T14; lia).
  assert (X13 : MLT + 4104 <= DCTX + 26684 \/ DCTX + 95992 <= MLT) by (clear - T15; lia).
  assert (TLS : Z.of_nat (length (map (Z_to_bv 8) (seq_table_bytes tLL))) <= 4104 /\ Z.of_nat (length (map (Z_to_bv 8) (seq_table_bytes tOF))) <= 2056 /\ Z.of_nat (length (map (Z_to_bv 8) (seq_table_bytes tML))) <= 4104)
    by (destruct TBL0 as ((_ & O1) & (_ & O2) & (_ & O3) & _); split; [apply tbl_len_LL; exact O1| split; [apply tbl_len_OF; exact O2 | apply tbl_len_ML; exact O3]]).
  destruct TLS as (LLL & LOF & LML).
  clear RG SIDE P1 P2 P3 P4 P5 P6 P7 P8 T7 T8 T9 T13 T14 T15.
  assert (MU : munch [(DST, DST + CAP); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (DCTX + 30368, DCTX + 30368 + 4); (SPV - 592, SPV)] m m) by apply munch_refl.
  assert (WM : wmono usegs m m) by apply wmono_refl.
  assert (MUL : munch [(SPV - 384, SPV)] m m) by apply munch_refl.
  assert (R0 : 592 <= SPV < 2^47 /\ 0 <= lo <= SPV - 592) by (clear - RA; lia).
  carve_frame 384%nat STK.
  (* [comment removed for export] *)
  hold PT. hold REP. hold HH1. hold HH3. hold H5V. hold H5O. hold BUF. hold LRD. hold XLIT. hold STK. hold TLL. hold TOF. hold TML. hold SQB.
  hold RG0. hold SIDE0. hold SEP0. hold TBL0. hold SINTRO. hold CONT. hold RA. hold MU.
  hold X1. hold X2. hold X3. hold X4. hold X5. hold X6. hold X7. hold X8. hold X9. hold X10. hold X11. hold X12. hold X13.
  kx_run [0x1ac40] 20%nat [KZRange SPV 592 (2^47); KZWr (SPV - 384) 384] [].
  kx_mem. unfold held in MU.
  unfold held in PT, REP, HH1, HH3, H5V, H5O, BUF, LRD, XLIT, STK, TLL, TOF, TML, SQB, X1, X2, X3, X4, X5, X6, X7.
  lazymatch type of MUL with munch _ _ ?m' => assert (LRD' : rdbl usegs m' LITP (LBE + WILDCOPY_OVERLENGTH)) by (eapply (rdbl_transport usegs _ m m'); [exact LRD | exact MUL | intros x Hx; left; cbn [outside]; unfold WILDCOPY_OVERLENGTH in *; split; [lia|exact I]]) end.
  lazymatch type of MUL with munch _ _ ?m' => assert (XLIT' : rdbl usegs m' (DCTX + 30372) (DCTX + 95940)) by (eapply (rdbl_transport usegs _ m m'); [exact XLIT | exact MUL | intros x Hx; left; cbn [outside]; split; [lia|exact I]]) end.
  lazymatch type of MUL with munch _ _ ?m' => transport_after_call usegs m m' MUL WM end.
  clear LRD XLIT MUL. rename LRD' into LRD. rename XLIT' into XLIT. unfold WILDCOPY_OVERLENGTH in LRD.
  apply seqs_prologue_frame384 in FR. destruct FR as (c0 & c8 & c16 & c24 & c32 & c40 & c48 & c56 & c64 & c72 & c80 & c88 & c96 & c104 & c112 & c120 & c128 & jbd & u176 & u184 & u192 & u200 & u208 & u216 & c224 & c232 & c240 & c248 & jseq & FR).
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (MUL : munch [(DCTX + 30004, DCTX + 30004 + 4); (SPV - 384, SPV)] mm mm) by apply munch_refl; assert (WML : wmono usegs mm mm) by apply wmono_refl end.
  unfold held in X8, X9, X10, X11, X12, X13.
  hold PT. hold BUF. hold STK. hold LRD. hold XLIT. hold TLL. hold TOF. hold TML. hold SQB. hold MU. hold WM. hold H5O.
  hold X2. hold X3. hold X4. hold X5. hold X6. hold X7. hold X8. hold X9. hold X10. hold X11. hold X12. hold X13.
  unfold held in RA.
  kx_autoLx [0x1d904; 0x1ca64] 60%nat
    [KZRange SPV 592 (2^47); KZRange DCTX 4096 (2^47); KZRange DST 4096 (2^47); KZRange CAP 32 (2^47); KZRange (DST + CAP) 4096 (2^47); KZRange LITP 4096 (2^47); KZRange LBE 4096 (2^47);
     KZRange nbSeq 1 98047; KZRange (zlen sq) 0 (2^47); KZRange SEQ 4096 (2^47);
     KZWr (SPV - 384) 384; KZWr (DCTX + 29976) 32; KZDisj (SPV - 384) 384 DCTX 95992]
    [].
  all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ca64) _ _ _ _) => first [kx_trap_fast | seqs_land_close] end).
  all: kx_mem; unfold held in LRD, XLIT, X3, X1, X10;
    lazymatch type of MUL with munch _ ?ma ?mb =>
      assert (LRD2 : rdbl usegs mb LITP (LBE + 32)) by (eapply (rdbl_transport usegs _ ma mb); [exact LRD | exact MUL | intros x Hx; left; cbn [outside]; split; [lia| split; [lia|exact I]]]);
      assert (XLIT2 : rdbl usegs mb (DCTX + 30372) (DCTX + 95940)) by (eapply (rdbl_transport usegs _ ma mb); [exact XLIT | exact MUL | intros x Hx; left; cbn [outside]; split; [lia| split; [lia|exact I]]]) end;
    unfold held in *;
    lazymatch type of MUL with munch _ ?ma ?mb => transport_after_call usegs ma mb MUL WML end.
  all: try replace (SPV + -384 + 136) with (SPV + -248) by lia.
  all: destruct (Z.eq_dec (zlen sq) 0) as [Z0|NZ0].
  2: { eapply (CONT (DST + CAP));
      [ eapply SINTRO; [exact RG0 | exact SIDE0 | exact SEP0 | exact TBL0 | exact NZ | cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws]; lia | cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws]; exact LV | cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws]; lia]
      | eapply seqs_iinv_eq;
        [ (unfold seqs_iinv; cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws]; split; [exact FR|]; split; [unfold dctx_ptrs; exact PT|]; split; [exact TLL|]; split; [exact TOF|]; split; [exact TML|]; split; [exact SQB|]; split; [exact LRD2|]; split; [exact XLIT2|]; split; [split; [unfold h5_vcells; exact H5O | exact H5L]|]; cbn [seqs_xinv]; rewrite FE1; unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation; split; [do 3 eexists; exact REP|]; split; [exact HH3|]; split; [exact BUF|]; split; [exact STK|]; split; [exact MU|]; split; [exact WM| lazymatch goal with MIx : mem_inv usegs ?mm |- mem_inv usegs ?mm => exact MIx end])
        | repeat f_equal; lia ] ]. }
  assert (AL16 : SPV mod 16 = 0) by (clear - TBL0; cbn [seqs_tables] in TBL0; destruct TBL0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & A16)); exact A16).
  lazymatch type of FR with rw_cells _ ?mm _ ?L =>
    rewrite <- (firstn_skipn 17 L) in FR; rewrite <- (firstn_skipn 1 (skipn 17 L)) in FR;
    assert (MUL3 : munch [(SPV - 384, SPV)] mm mm) by apply munch_refl end.
  apply rw_cells_app in FR. destruct FR as (ZPRE & FR). apply rw_cells_app in FR. destruct FR as (ZBDC & ZPOST).
  cbn [firstn skipn] in ZPRE, ZBDC, ZPOST.
  lazymatch type of ZBDC with rw_cells _ _ ?A _ => replace A with (SPV + -248) in ZBDC by (cbn [cells_size csize Nat.add]; lia) end.
  pose proof seqd_bit_init_proof as BIP. unfold seqd_bit_init_stmt, PZD_BITINIT in BIP.
  eapply evt_cut.
  { eapply (BIP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SPV + -248) SEQ (zlen sq) (map (Z_to_bv 8) sq) _);
      [ assumption | exact ZBDC | clear - AL16; lia | exact SQB | first [exact LSQ | unfold zlen; rewrite length_map; reflexivity]
      | clear - RA; lia | clear - RA; lia | clear - RA; lia | clear - RA Z0; lia | clear - RA X4 Z0; lia ]. }
  clear AL16 BIP ZBDC.
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mcl & r & -> & MUc & WMc & MIc & ZRES).
  destruct ZRES as [(_ & ZN1 & _) | (ZER & ZHR & zbs & ZBDC2)]; [exfalso; clear - ZN1 Z0; lia|].
  lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?nr)) _ _ _ _) =>
    replace (ret_pc (Z_to_bv 64 nr)) with (Z_to_bv 64 nr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
  lazymatch type of MUc with munch _ ?ma ?mb => transport_after_call usegs ma mb MUc WMc end.
  lazymatch type of ZPRE with rw_cells _ _ _ ?c1 => lazymatch type of ZPOST with rw_cells _ _ ?A2 ?c2 =>
    assert (FR2 : rw_cells usegs mcl (SPV + -384) (c1 ++ [CB 40 zbs] ++ c2))
      by (apply rw_cells_app; split; [exact ZPRE | apply rw_cells_app; split;
          [ lazymatch goal with |- rw_cells _ _ ?A _ => replace A with (SPV + -248) by (cbn [cells_size csize Nat.add]; lia) end; exact ZBDC2
          | lazymatch goal with |- rw_cells _ _ ?A _ => replace A with A2 by (cbn [cells_size csize Nat.add]; lia) end; exact ZPOST ]]) end end.
  clear ZPRE ZPOST ZBDC2. cbn [app] in FR2.
  apply zd_is_error_true_iff in ZER.
  try hold DAL.
  kx_autoLx [0x1c6fc] 12%nat [KZRange SPV 592 (2^47); KZRange r (2^64 - 119) (2^64 - 1)] [].
  all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ca64) _ _ _ _) => first [kx_trap_fast | seqs_land_close] end).
  all: kx_mem.
  lazymatch type of MUL3 with munch _ ?ma ?mb =>
    assert (LRD3 : rdbl usegs mb LITP (LBE + 32)) by (eapply (rdbl_transport usegs _ ma mb); [exact LRD2 | exact MUL3 | intros xq Hxq; left; cbn [outside]; split; [clear - Hxq X3; lia | exact I]]);
    assert (XLIT3 : rdbl usegs mb (DCTX + 30372) (DCTX + 95940)) by (eapply (rdbl_transport usegs _ ma mb); [exact XLIT2 | exact MUL3 | intros xq Hxq; left; cbn [outside]; split; [clear - Hxq X1 RA; lia | exact I]]) end.
  lazymatch type of RG0 with seqs_ranges ?PP => pose proof (seqs_iexit PP (DST + CAP) LITP LBE 2) as IEXIT end.
  cbn [seqs_post v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in IEXIT.
  eapply IEXIT;
    [ exact RG0
    | (unfold seqs_iinv; cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws]; split; [exact FR2|]; split; [unfold dctx_ptrs; exact PT|]; split; [exact TLL|]; split; [exact TOF|]; split; [exact TML|]; split; [exact SQB|]; split; [exact LRD3|]; split; [exact XLIT3|]; split; [split; [unfold h5_vcells; exact H5O | exact H5L]|]; cbn [seqs_xinv]; rewrite FE1; unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation; split; [do 3 eexists; exact REP|]; split; [exact HH3|]; split; [exact BUF|]; split; [exact STK|]; split; [exact MU|]; split; [exact WM| lazymatch goal with MIx : mem_inv usegs ?mm |- mem_inv usegs ?mm => exact MIx end])
    | reflexivity | reflexivity | lia | left; reflexivity ].
Qed.
