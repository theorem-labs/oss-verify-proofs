(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_ibase RZ_huf_iface seqD_kit_initfse seqD_kit_initfse_proof.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seql_ifse_call : forall P OEND LLO LEND LOCV m1 (c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 c168 c176 c184 c216 c224 c232 cw : word) (jpad : list byte) (bc ptr : Z)
    (sa : list cell) (v0 v1 : word) (sb : list cell) (p0 p1 p2 : word) (jring jseq : list byte) (k : seq_kind) (t : seq_table) (T STP B : Z) (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  seql_static P OEND LLO LEND LOCV ->
  seql_iinv P OEND LLO LEND LOCV m1 (seql_ifr P OEND LEND c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 c168 c176 c184 c216 c224 c232 (bitd_cells cw (Z_to_bv 64 bc) jpad ptr (y_SEQ P)) (sa ++ [C8 v0; C8 v1] ++ sb) p0 p1 p2 jring jseq) ->
  (k = K_LL /\ t = y_tLL P /\ T = y_LLT P) \/ (k = K_OF /\ t = y_tOF P /\ T = y_OFT P) \/ (k = K_ML /\ t = y_tML P /\ T = y_MLT P) ->
  Z.of_nat (cells_size sa) = 0 \/ Z.of_nat (cells_size sa) = 16 \/ Z.of_nat (cells_size sa) = 32 ->
  STP = y_SPV P + -400 + Z.of_nat (cells_size sa) ->
  seql_ibits P B bc ptr -> B <= 82 ->
  (forall m2 (t0' a1' a2' a3' a4' a5' a6' a7' cw' : word) (jpad' : list byte) (bc' ptr' st : Z),
     seql_iinv P OEND LLO LEND LOCV m2 (seql_ifr P OEND LEND c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 c168 c176 c184 c216 c224 c232 (bitd_cells cw' (Z_to_bv 64 bc') jpad' ptr' (y_SEQ P)) (sa ++ [C8 (Z_to_bv 64 st); C8 (Z_to_bv 64 (T + 8))] ++ sb) p0 p1 p2 jring jseq) ->
     seql_ibits P (B + 9) bc' ptr' -> 0 <= st < 2^(st_log t) ->
     evt usegs Q (MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 STP) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m2 (seg_rom usegs))) ->
  evt usegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 STP) (Z_to_bv 64 (y_SPV P + -440)) (Z_to_bv 64 T) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 PZD_INITFSE) fc None m1 (seg_rom usegs)).
Proof.
  intros P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 c168 c176 c184 c216 c224 c232 cw jpad bc ptr sa v0 v1 sb p0 p1 p2 jring jseq k t T STP B Q
    ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ST INV KT SA HSTP IB HB K.
  pose proof (seql_iinv_frame P OEND LLO LEND LOCV m1 _ ST INV) as TRANS.
  pose proof (seql_iinv_mi _ _ _ _ _ _ _ INV) as MI.
  destruct INV as (FR & _ & TLL & TOF & TML & SQB & _).
  destruct IB as (IB1 & IB2). unfold bit_ok in IB2.
  assert (TF : bytes_at usegs m1 T (map (Z_to_bv 8) (seq_table_bytes t)) /\ seq_table_ok k t /\ 4096 <= T < 2^47 /\ T mod 4 = 0 /\
               (T + 8 * (1 + 2^(st_log t)) <= y_lo P \/ y_SPV P <= T)).
  { clear - ST KT TLL TOF TML.
    destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
    cbn [seql_static y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in *.
    sd_static_open ST. unfold held in KT.
    destruct KT as [(-> & -> & ->)|[(-> & -> & ->)|(-> & -> & ->)]].
    - pose proof OKLL as (TL & _). cbn [kind_maxLog] in TL.
      assert (PW : 2^(st_log tLL) <= 2^9) by (apply Z.pow_le_mono_r; lia). change (2^9) with 512 in PW.
      split; [exact TLL|]. split; [exact OKLL|]. split; [lia|]. split; [exact AL1|]. unfold held in S28. clear - S28 S18 PW. lia.
    - pose proof OKOF as (TL & _). cbn [kind_maxLog] in TL.
      assert (PW : 2^(st_log tOF) <= 2^8) by (apply Z.pow_le_mono_r; lia). change (2^8) with 256 in PW.
      split; [exact TOF|]. split; [exact OKOF|]. split; [lia|]. split; [exact AL2|]. unfold held in S29. clear - S29 S18 PW. lia.
    - pose proof OKML as (TL & _). cbn [kind_maxLog] in TL.
      assert (PW : 2^(st_log tML) <= 2^9) by (apply Z.pow_le_mono_r; lia). change (2^9) with 512 in PW.
      split; [exact TML|]. split; [exact OKML|]. split; [lia|]. split; [exact AL3|]. unfold held in S30. clear - S30 S18 PW. lia. }
  destruct TF as (TB & OK & T1 & T2 & T3).
  destruct P as [ra' gp' tp' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' F' fc' m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in *.
  sd_static_open ST. unfold held in SA, T3, S25.
  assert (LSQ : Z.of_nat (length (map (Z_to_bv 8) sq)) = zlen sq) by (unfold zlen; rewrite length_map; reflexivity).
  assert (BDA : (SPV + -440) mod 8 = 0) by (clear - AL4; Z.div_mod_to_equations; lia).
  assert (STA : STP mod 8 = 0) by (rewrite HSTP; clear - AL4 SA; Z.div_mod_to_equations; lia).
  unfold seql_ifr in FR.
  cbn [y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in FR.
  apply rw_cells_app in FR. destruct FR as (F0 & FR).
  apply rw_cells_app in FR. destruct FR as (BDC & FR).
  apply rw_cells_app in FR. destruct FR as (STL & F2).
  apply rw_cells_app in STL. destruct STL as (SAC & STL).
  apply rw_cells_app in STL. destruct STL as (STC & SBC).
  assert (SZ : forall a b : word, Z.of_nat (cells_size (sa ++ [C8 a; C8 b] ++ sb)) = Z.of_nat (cells_size sa) + 16 + Z.of_nat (cells_size sb))
    by (intros a b; rewrite !cells_size_app; cbn [cells_size csize Nat.add]; lia).
  rewrite SZ in F2.
  match type of BDC with rw_cells _ _ ?A _ => replace A with (SPV + -440) in BDC by (cbn [cells_size csize Nat.add]; lia) end.
  match type of SAC with rw_cells _ _ ?A _ => replace A with (SPV + -400) in SAC by (cbn [cells_size csize Nat.add bitd_cells]; lia) end.
  match type of STC with rw_cells _ _ ?A _ => replace A with STP in STC by (cbn [cells_size csize Nat.add bitd_cells]; lia) end.
  match type of SBC with rw_cells _ _ ?A _ => replace A with (STP + 16) in SBC by (cbn [cells_size csize Nat.add bitd_cells]; lia) end.
  match type of F2 with rw_cells _ _ ?A _ => replace A with (STP + 16 + Z.of_nat (cells_size sb)) in F2 by (cbn [cells_size csize Nat.add bitd_cells]; lia) end.
  eapply evt_cut.
  { eapply (zd_initfse_proof ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 (SPV + -440) STP T SEQ (zlen sq) B bc ptr cw v0 v1 jpad (map (Z_to_bv 8) sq) k t);
      first [ exact MI | exact BDC | exact STC | exact TB | exact OK | exact SQB | exact LSQ | exact IB2 | exact BDA | exact STA | exact T2 | exact I | lia ]. }
  intros ms' (t0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m2 & cw' & bc' & jpad' & ptr' & st & -> & MU & WM & MI2 & BDC2 & STC2 & HST & HBC & HBP).
  eapply (K m2 t0' a1' a2' a3' a4' a5' a6' a7' cw' jpad' bc' ptr' st); [ | unfold seql_ibits; cbn [y_SEQ y_sq]; split; [lia | exact HBP] | exact HST ].
  eapply TRANS; [ | exact WM | exact MI2 | ].
  { eapply munch_weaken; [|exact MU]. unfold sub_fp. intros x HX. cbn [outside] in HX |- *. destruct HX as (HX & _). split; [lia|]. split; [lia | exact I]. }
  unfold seql_ifr.
  cbn [y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws].
  apply rw_cells_app. split.
  { eapply rw_cells_transport; [exact F0 | exact MU | exact WM | ]. cbn [disjoint_from cells_size csize Nat.add]. split; [lia | split; [lia | exact I]]. }
  apply rw_cells_app. split.
  { match goal with |- rw_cells _ _ ?A _ => replace A with (SPV + -440) by (cbn [cells_size csize Nat.add]; lia) end. exact BDC2. }
  apply rw_cells_app. split.
  { apply rw_cells_app. split.
    { match goal with |- rw_cells _ _ ?A _ => replace A with (SPV + -400) by (cbn [cells_size csize Nat.add bitd_cells]; lia) end.
      eapply rw_cells_transport; [exact SAC | exact MU | exact WM | ]. cbn [disjoint_from]. split; [lia | split; [lia | exact I]]. }
    apply rw_cells_app. split.
    { match goal with |- rw_cells _ _ ?A _ => replace A with STP by (cbn [cells_size csize Nat.add bitd_cells]; lia) end. exact STC2. }
    match goal with |- rw_cells _ _ ?A _ => replace A with (STP + 16) by (cbn [cells_size csize Nat.add bitd_cells]; lia) end.
    eapply rw_cells_transport; [exact SBC | exact MU | exact WM | ]. cbn [disjoint_from]. split; [lia | split; [lia | exact I]]. }
  rewrite SZ.
  match goal with |- rw_cells _ _ ?A _ => replace A with (STP + 16 + Z.of_nat (cells_size sb)) by (cbn [cells_size csize Nat.add bitd_cells]; lia) end.
  eapply rw_cells_transport; [exact F2 | exact MU | exact WM | ]. cbn [disjoint_from]. split; [lia | split; [lia | exact I]].
Qed.


(* [comment removed for export] *)
Lemma seql_ifse_LL : forall P OEND LLO LEND LOCV, seql_static P OEND LLO LEND LOCV -> ai_i2 P OEND LLO LEND LOCV -> ai_i1 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST CONT. unfold ai_i1.
  intros m1 c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 c176 c184 c216 c224 c232 cw u288 u296 u304 u312 u320 u328 p0 p1 p2 jpad jring jseq bc ptr x5 x6 x7 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 INV IB HN.
  unfold ai_i2 in CONT.
  eapply (seql_ifse_call P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 (Z_to_bv 64 (2^60)) c176 c184 c216 c224 c232 cw jpad bc ptr [] u288 u296 [C8 u304; C8 u312; C8 u320; C8 u328] p0 p1 p2 jring jseq K_LL (y_tLL P));
    [ exact ST | exact INV | left; repeat split; reflexivity | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia | exact IB | lia | ].
  intros m2 t0' a1' a2' a3' a4' a5' a6' a7' cw' jpad' bc' ptr' st INV2 IB2 HST.
  rewrite ret_pc_even by (first [reflexivity | lia]).
  eapply (CONT m2 c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 c176 c184 c216 c224 c232 cw' u304 u312 u320 u328 p0 p1 p2 jpad' jring jseq bc' ptr' st); [exact INV2 | exact IB2 | exact HN | exact HST].
Qed.

(* [comment removed for export] *)
Lemma seql_ifse_OF : forall P OEND LLO LEND LOCV, seql_static P OEND LLO LEND LOCV -> ai_i4 P OEND LLO LEND LOCV -> ai_i3 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST CONT. unfold ai_i3.
  intros m1 c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 c176 c184 c216 c224 c232 cw u304 u312 u320 u328 p0 p1 p2 jpad jring jseq bc ptr sLL x5 x6 x7 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 INV IB HN HS.
  unfold ai_i4 in CONT.
  eapply (seql_ifse_call P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 (Z_to_bv 64 (2^60)) c176 c184 c216 c224 c232 cw jpad bc ptr [C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (y_LLT P + 8))] u304 u312 [C8 u320; C8 u328] p0 p1 p2 jring jseq K_OF (y_tOF P));
    [ exact ST | exact INV | right; left; repeat split; reflexivity | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia | exact IB | lia | ].
  intros m2 t0' a1' a2' a3' a4' a5' a6' a7' cw' jpad' bc' ptr' st INV2 IB2 HST.
  rewrite ret_pc_even by (first [reflexivity | lia]).
  eapply (CONT m2 c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 c176 c184 c216 c224 c232 cw' u320 u328 p0 p1 p2 jpad' jring jseq bc' ptr' sLL st); [exact INV2 | exact IB2 | exact HN | exact HS | exact HST].
Qed.

(* [comment removed for export] *)
Lemma seql_ifse_ML : forall P OEND LLO LEND LOCV, seql_static P OEND LLO LEND LOCV -> ai_i6 P OEND LLO LEND LOCV -> ai_i5 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST CONT. unfold ai_i5.
  intros m1 c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 c176 c184 c216 c224 c232 cw u320 u328 p0 p1 p2 jpad jring jseq bc ptr sLL sOF x5 x6 x7 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 INV IB HN HS1 HS2.
  unfold ai_i6 in CONT.
  eapply (seql_ifse_call P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 (Z_to_bv 64 (2^60)) c176 c184 c216 c224 c232 cw jpad bc ptr [C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (y_LLT P + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (y_OFT P + 8))] u320 u328 [] p0 p1 p2 jring jseq K_ML (y_tML P));
    [ exact ST | exact INV | right; right; repeat split; reflexivity | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia | exact IB | lia | ].
  intros m2 t0' a1' a2' a3' a4' a5' a6' a7' cw' jpad' bc' ptr' st INV2 IB2 HST.
  rewrite ret_pc_even by (first [reflexivity | lia]).
  eapply (CONT m2 c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 c176 c184 c216 c224 c232 cw' p0 p1 p2 jpad' jring jseq bc' ptr' sLL sOF st); [exact INV2 | exact IB2 | exact HN | exact HS1 | exact HS2 | exact HST].
Qed.
