From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface seqD_kit_initfse seqD_kit_initfse_proof RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_lbase RZ_seq_s_lkit RZ_seq_s_ibase.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac sif_h H X E1 E2 := lazymatch type of H with rw_cells _ _ ?A _ => replace A with X in H by (rewrite ?cells_size_app; cbn [cells_size csize Nat.add]; clear - E1 E2; lia) end.
Ltac sif_g X E1 E2 := lazymatch goal with |- rw_cells _ _ ?A _ => replace A with X by (rewrite ?cells_size_app; cbn [cells_size csize Nat.add]; clear - E1 E2; lia) end.

Lemma seqs_ifse_call : forall (P : ssp) (OEND LLO LEND LOCV : Z) (Q : machine_state -> Prop) (m1 : fmem)
    (c0 c8 c16 c24 c40 c72 c104 c128 cw : word) (jpad jseq : list byte) (bc ptr : Z) (stA stB : list cell) (st0 tb0 p0 p1 p2 : word)
    (STP T B RA : Z) (k : seq_kind) (t : seq_table)
    (y5 y6 y7 y8 y9 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
  seqs_static P OEND LLO LEND LOCV ->
  seqs_iinv P OEND LLO LEND LOCV m1 (seqs_ifr P OEND LEND c0 c8 c16 c24 c40 c72 c104 c128 [C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (v_SEQ P)); C8 (Z_to_bv 64 (v_SEQ P + 8))] (stA ++ [C8 st0; C8 tb0] ++ stB) p0 p1 p2 jseq) ->
  STP = v_SPV P + -208 + Z.of_nat (cells_size stA) ->
  (cells_size stA = 0 \/ cells_size stA = 16 \/ cells_size stA = 32)%nat ->
  (cells_size stA + cells_size stB = 32)%nat ->
  (T = v_LLT P /\ t = v_tLL P /\ k = K_LL) \/ (T = v_OFT P /\ t = v_tOF P /\ k = K_OF) \/ (T = v_MLT P /\ t = v_tML P /\ k = K_ML) ->
  seqs_ibits P B bc ptr -> B <= 82 ->
  ret_pc (Z_to_bv 64 RA) = Z_to_bv 64 RA ->
  (forall (m2 : fmem) (cw2 : word) (jpad2 : list byte) (bc2 ptr2 st : Z) (z5 z11 z12 z13 z14 z15 z16 z17 : word),
     seqs_iinv P OEND LLO LEND LOCV m2 (seqs_ifr P OEND LEND c0 c8 c16 c24 c40 c72 c104 c128 [C8 cw2; C4 (Z_to_bv 64 bc2); CB 4 jpad2; C8 (Z_to_bv 64 ptr2); C8 (Z_to_bv 64 (v_SEQ P)); C8 (Z_to_bv 64 (v_SEQ P + 8))] (stA ++ [C8 (Z_to_bv 64 st); C8 (Z_to_bv 64 (T + 8))] ++ stB) p0 p1 p2 jseq) ->
     seqs_ibits P (B + 9) bc2 ptr2 -> 0 <= st < 2^(st_log t) ->
     evt usegs Q (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) z5 y6 y7 y8 y9 (Z_to_bv 64 STP) z11 z12 z13 z14 z15 z16 z17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) (v_F P) (Z_to_bv 64 RA) (v_fc P) None m2 (seg_rom usegs))) ->
  evt usegs Q (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) y5 y6 y7 y8 y9 (Z_to_bv 64 STP) (Z_to_bv 64 (v_SPV P + -248)) (Z_to_bv 64 T) y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31) (v_F P) (Z_to_bv 64 PZD_INITFSE) (v_fc P) None m1 (seg_rom usegs)).
Proof.
  intros P OEND LLO LEND LOCV Q m1 c0 c8 c16 c24 c40 c72 c104 c128 cw jpad jseq bc ptr stA stB st0 tb0 p0 p1 p2 STP T B RA k t
    y5 y6 y7 y8 y9 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 ST INV ESTP HSA HSB HTAB IB HB HRA K.
  pose proof (seqs_iinv_frame P OEND LLO LEND LOCV m1 _ ST INV) as TRANS.
  pose proof (seqs_iinv_mi _ _ _ _ _ _ _ INV) as MI.
  destruct INV as (FR & PT & TLL & TOF & TML & SQB & _). destruct IB as (IB1 & IB2).
  unfold seqs_ifr in FR.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in *.
  apply rw_cells_app in FR. destruct FR as (PRE & FR).
  apply rw_cells_app in FR. destruct FR as (BDC & FR).
  apply rw_cells_app in FR. destruct FR as (STC & POST).
  sif_h BDC (SPV + -248) ESTP HSB. sif_h STC (SPV + -208) ESTP HSB. sif_h POST (SPV + -160) ESTP HSB.
  apply rw_cells_app in STC. destruct STC as (SA & STC).
  sif_h STC STP ESTP HSB.
  apply rw_cells_app in STC. destruct STC as (TWO & SB).
  sif_h SB (STP + 16) ESTP HSB.
  cbn [seqs_static] in ST. sd_static_open ST.
  try unfold held in HSA. try unfold held in HTAB. try unfold held in S25. try unfold held in S28. try unfold held in S29. try unfold held in S30.
  assert (TF : bytes_at usegs m1 T (map (Z_to_bv 8) (seq_table_bytes t)) /\ seq_table_ok k t /\ 4096 <= T < 2^47 /\ T mod 4 = 0 /\
               (T + 8 * (1 + 2^(st_log t)) <= lo \/ SPV <= T)).
  { destruct HTAB as [(-> & -> & ->) | [(-> & -> & ->) | (-> & -> & ->)]].
    - pose proof OKLL as (RT & _). cbn [kind_maxLog] in RT.
      assert (RP : 2^(st_log tLL) <= 512) by (change 512 with (2^9); apply Z.pow_le_mono_r; lia).
      split; [exact TLL|]. split; [exact OKLL|]. split; [clear - S21; lia|]. split; [exact AL1|]. clear - S28 RP; lia.
    - pose proof OKOF as (RT & _). cbn [kind_maxLog] in RT.
      assert (RP : 2^(st_log tOF) <= 256) by (change 256 with (2^8); apply Z.pow_le_mono_r; lia).
      split; [exact TOF|]. split; [exact OKOF|]. split; [clear - S22; lia|]. split; [exact AL2|]. clear - S29 RP; lia.
    - pose proof OKML as (RT & _). cbn [kind_maxLog] in RT.
      assert (RP : 2^(st_log tML) <= 512) by (change 512 with (2^9); apply Z.pow_le_mono_r; lia).
      split; [exact TML|]. split; [exact OKML|]. split; [clear - S23; lia|]. split; [exact AL3|]. clear - S30 RP; lia. }
  clear HTAB. destruct TF as (TB & OK & TR & TA & TD).
  assert (ABD : (SPV + -248) mod 8 = 0) by (clear - AL4; lia).
  assert (ASTP : STP mod 8 = 0) by (clear - AL4 ESTP HSA; lia).
  clear AL1 AL2 AL3 AL4.
  pose proof zd_initfse_proof as IFP. unfold zd_initfse_stmt, zd_initfse_stmt_if in IFP.
  eapply evt_cut.
  { eapply (IFP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (SPV + -248) STP T SEQ (zlen sq) B bc ptr cw st0 tb0 jpad (map (Z_to_bv 8) sq) k t);
      [ exact MI | exact BDC | exact TWO | exact TB | exact OK | exact SQB | unfold zlen; rewrite length_map; reflexivity
      | clear - S15; lia | clear - S18; lia | clear - S17; lia | clear - S18 ESTP; lia | clear - S17 ESTP HSB; lia
      | clear - TR; lia | clear - TR; lia | clear - S13; lia | clear - S14; lia
      | exact ABD | exact ASTP | exact TA
      | left; clear - ESTP; lia | clear - S25 S18; lia | clear - S25 S18 ESTP HSB; lia
      | clear - TD S18; lia | clear - TD S18 ESTP HSB; lia
      | exact IB1 | exact HB | exact IB2 | exact I ]. }
  clear ABD ASTP TA IFP.
  intros ms' (z5 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & m' & cw' & bc' & jpad' & ptr' & st & -> & MU & WM & MI' & BDC' & STC' & HST & HBC' & HBOK').
  rewrite HRA.
  apply (K m' cw' jpad' bc' ptr' st z5 z11 z12 z13 z14 z15 z16 z17); [| split; [exact HBC' | exact HBOK'] | exact HST].
  apply (TRANS m').
  - eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]. intros x Hx. clear - Hx ESTP HSB. lia.
  - exact WM.
  - exact MI'.
  - unfold seqs_ifr.
    cbn [v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws].
    apply rw_cells_app; split.
    { eapply rw_cells_transport; [exact PRE | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; clear - ESTP HSB; lia]. }
    apply rw_cells_app; split.
    { sif_g (SPV + -248) ESTP HSB. exact BDC'. }
    sif_g (SPV + -208) ESTP HSB.
    apply rw_cells_app; split.
    2: { sif_g (SPV + -160) ESTP HSB. eapply rw_cells_transport; [exact POST | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; clear - ESTP HSB; lia]. }
    apply rw_cells_app; split.
    { eapply rw_cells_transport; [exact SA | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; clear - ESTP HSB; lia]. }
    sif_g STP ESTP HSB.
    apply rw_cells_app; split.
    { exact STC'. }
    sif_g (STP + 16) ESTP HSB.
    eapply rw_cells_transport; [exact SB | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; clear - ESTP HSB; lia].
Qed.
