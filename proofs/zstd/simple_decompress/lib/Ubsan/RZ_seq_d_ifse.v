(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface huf411_kit_rs seqD_kit_initfse seqD_kit_initfse_proof RZ_seq_iface RZ_seq_kit RZ_seq_d_base RZ_seq_d_lbase RZ_seq_d_lkit RZ_seq_d_ibase.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seqd_iinv_eq : forall P LEND m1 fr fr', seqd_iinv P LEND m1 fr -> fr = fr' -> seqd_iinv P LEND m1 fr'.
Proof. intros P LEND m1 fr fr' H E. subst fr'. exact H. Qed.

Lemma seqd_ifse_call : forall P OEND LEND m1 (c0 c8 c16 c48 c72 c80 c88 cw : word) (jpad : list byte) (bc ptr : Z)
    (sa : list cell) (v0 v1 : word) (sb : list cell) (p0 p1 p2 : word) (jseq : list byte) (k : seq_kind) (t : seq_table) (T STP B : Z) (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  seqd_static P OEND LEND ->
  seqd_iinv P LEND m1 (seqd_ifr P OEND LEND c0 c8 c16 c48 c72 c80 c88 (bitd_cells cw (Z_to_bv 64 bc) jpad ptr (q_SEQ P)) (sa ++ [C8 v0; C8 v1] ++ sb) p0 p1 p2 jseq) ->
  (k = K_LL /\ t = q_tLL P /\ T = q_LLT P) \/ (k = K_OF /\ t = q_tOF P /\ T = q_OFT P) \/ (k = K_ML /\ t = q_tML P /\ T = q_MLT P) ->
  Z.of_nat (cells_size sa) = 0 \/ Z.of_nat (cells_size sa) = 16 \/ Z.of_nat (cells_size sa) = 32 ->
  Z.of_nat (cells_size sa) + Z.of_nat (cells_size sb) = 32 ->
  STP = q_SPV P + -208 + Z.of_nat (cells_size sa) ->
  seqd_ibits P B bc ptr -> B <= 82 ->
  (forall m2 (t0' a1' a2' a3' a4' a5' a6' a7' cw' : word) (jpad' : list byte) (bc' ptr' st : Z),
     seqd_iinv P LEND m2 (seqd_ifr P OEND LEND c0 c8 c16 c48 c72 c80 c88 (bitd_cells cw' (Z_to_bv 64 bc') jpad' ptr' (q_SEQ P)) (sa ++ [C8 (Z_to_bv 64 st); C8 (Z_to_bv 64 (T + 8))] ++ sb) p0 p1 p2 jseq) ->
     seqd_ibits P (B + 9) bc' ptr' -> 0 <= st < 2^(st_log t) ->
     evt usegs Q (MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 STP) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m2 (seg_rom usegs))) ->
  evt usegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 STP) (Z_to_bv 64 (q_SPV P + -248)) (Z_to_bv 64 T) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 PZD_INITFSE) fc None m1 (seg_rom usegs)).
Proof.
  intros P OEND LEND m1 c0 c8 c16 c48 c72 c80 c88 cw jpad bc ptr sa v0 v1 sb p0 p1 p2 jseq k t T STP B Q
    ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ST INV KT SA SAB HSTP IB HB K.
  pose proof (seqd_iinv_frame P OEND LEND m1 _ ST INV) as TRANS.
  pose proof (seqd_iinv_mi _ _ _ _ INV) as MI.
  destruct INV as (FR0 & _ & TLL & TOF & TML & SQB & _).
  destruct IB as (IB1 & IB2). unfold bit_ok in IB2.
  assert (SS : forall a b : word, cells_size (sa ++ [C8 a; C8 b] ++ sb) = 48%nat)
    by (intros a b; rewrite !cells_size_app; cbn [cells_size csize Nat.add]; clear - SAB; lia).
  pose proof (fun m' bd' st' => seqd_ifr_join m1 m' P OEND LEND c0 c8 c16 c48 c72 c80 c88 (bitd_cells cw (Z_to_bv 64 bc) jpad ptr (q_SEQ P)) (sa ++ [C8 v0; C8 v1] ++ sb) bd' st' p0 p1 p2 jseq FR0 eq_refl (SS v0 v1)) as JOIN.
  pose proof FR0 as FR. unfold seqd_ifr in FR.
  apply rw_cells_app in FR as (_ & FR). apply rw_cells_app in FR as (FBD & FR). apply rw_cells_app in FR as (FST & _).
  apply rw_cells_app in FST as (FSA & FST). apply rw_cells_app in FST as (FV & FSB).
  assert (EH : Z.of_nat (cells_size (seqd_ifr_hd P OEND LEND c0 c8 c16 c48 c72 c80 c88)) = 104) by reflexivity.
  assert (EB : Z.of_nat (cells_size (bitd_cells cw (Z_to_bv 64 bc) jpad ptr (q_SEQ P))) = 40) by reflexivity.
  assert (EV : Z.of_nat (cells_size [C8 v0; C8 v1]) = 16) by reflexivity.
  rewrite EH in FBD, FSA, FV, FSB. rewrite EB in FSA, FV, FSB. rewrite EV in FSB. clear EH EB EV FR0.
  replace (q_SPV P + -352 + 104) with (q_SPV P + -248) in FBD by lia.
  replace (q_SPV P + -352 + 104 + 40) with (q_SPV P + -208) in FSA by lia.
  replace (q_SPV P + -352 + 104 + 40 + Z.of_nat (cells_size sa)) with STP in FV by (clear - HSTP; lia).
  replace (q_SPV P + -352 + 104 + 40 + Z.of_nat (cells_size sa) + 16) with (STP + 16) in FSB by (clear - HSTP; lia).
  destruct P as [ra' gp' tp' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' F' fc' m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_static q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in *.
  sd_static_open ST. unfold held in SA.
  assert (TF : bytes_at usegs m1 T (map (Z_to_bv 8) (seq_table_bytes t)) /\ seq_table_ok k t /\ 4096 <= T < 2^47 /\ T mod 4 = 0 /\
               (T + 8 * (1 + 2^(st_log t)) <= lo \/ SPV <= T)).
  { clear - KT TLL TOF TML OKLL OKOF OKML ALLL ALOF ALML S21 S22 S23 S28 S29 S30.
    destruct KT as [(-> & -> & ->)|[(-> & -> & ->)|(-> & -> & ->)]].
    - pose proof OKLL as (TL & _). cbn [kind_maxLog] in TL.
      assert (PW : 2^(st_log tLL) <= 2^9) by (apply Z.pow_le_mono_r; lia). change (2^9) with 512 in PW.
      split; [exact TLL|]. split; [exact OKLL|]. split; [unfold held in S21; clear - S21; lia|]. split; [exact (rsk_al_e _ _ ALLL)|].
      unfold held in S28. clear - S28 PW. lia.
    - pose proof OKOF as (TL & _). cbn [kind_maxLog] in TL.
      assert (PW : 2^(st_log tOF) <= 2^8) by (apply Z.pow_le_mono_r; lia). change (2^8) with 256 in PW.
      split; [exact TOF|]. split; [exact OKOF|]. split; [unfold held in S22; clear - S22; lia|]. split; [exact (rsk_al_e _ _ ALOF)|].
      unfold held in S29. clear - S29 PW. lia.
    - pose proof OKML as (TL & _). cbn [kind_maxLog] in TL.
      assert (PW : 2^(st_log tML) <= 2^9) by (apply Z.pow_le_mono_r; lia). change (2^9) with 512 in PW.
      split; [exact TML|]. split; [exact OKML|]. split; [unfold held in S23; clear - S23; lia|]. split; [exact (rsk_al_e _ _ ALML)|].
      unfold held in S30. clear - S30 PW. lia. }
  destruct TF as (TB & OK & (T1a & T1b) & T2 & T3).
  pose proof (rsk_al_e _ _ ALSP) as AL16.
  assert (BDA : (SPV + -248) mod 8 = 0) by (clear - AL16; Z.div_mod_to_equations; lia).
  assert (STA : STP mod 8 = 0).
  { rewrite HSTP. destruct SA as [E|[E|E]]; rewrite E; clear - AL16; Z.div_mod_to_equations; lia. }
  clear AL16.
  assert (LSQ : Z.of_nat (length (map (Z_to_bv 8) sq)) = zlen sq) by (unfold zlen; rewrite length_map; reflexivity).
  assert (N1 : 1 <= zlen sq) by (clear - S15; unfold held in S15; lia).
  assert (Q13 : 4096 <= SEQ) by (clear - S13; unfold held in S13; lia).
  assert (Q14 : SEQ + zlen sq < 2^47) by (clear - S14; unfold held in S14; lia).
  assert (R1 : 4096 <= SPV + -248) by (clear - S18; unfold held in S18; lia).
  assert (R2 : SPV + -248 + 40 < 2^47) by (clear - S17; unfold held in S17; lia).
  assert (R3 : 4096 <= STP) by (clear - S18 HSTP SA; unfold held in S18; lia).
  assert (R4 : STP + 16 < 2^47) by (clear - S17 HSTP SA; unfold held in S17; lia).
  assert (D1 : SPV + -248 + 40 <= STP \/ STP + 16 <= SPV + -248) by (clear - HSTP SA; lia).
  assert (D2 : SPV + -248 + 40 <= SEQ \/ SEQ + zlen sq <= SPV + -248) by (clear - S25 S18; unfold held in S25, S18; lia).
  assert (D3 : STP + 16 <= SEQ \/ SEQ + zlen sq <= STP) by (clear - S25 S18 HSTP SA; unfold held in S25, S18; lia).
  assert (D4 : SPV + -248 + 40 <= T \/ T + 8 * (1 + 2^(st_log t)) <= SPV + -248) by (clear - T3 S18; unfold held in S18; lia).
  assert (D5 : STP + 16 <= T \/ T + 8 * (1 + 2^(st_log t)) <= STP) by (clear - T3 S18 HSTP SA; unfold held in S18; lia).
  eapply evt_cut.
  { eapply (zd_initfse_proof ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 (SPV + -248) STP T SEQ (zlen sq) B bc ptr cw v0 v1 jpad (map (Z_to_bv 8) sq) k t);
      first [ exact MI | exact FBD | exact FV | exact TB | exact OK | exact SQB | exact LSQ | exact IB2 | exact I | assumption ]. }
  intros ms' (t0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m2 & cw' & bc' & jpad' & ptr' & st & -> & MU & WM & MI2 & BDC2 & STC2 & HST & HBC & HBP).
  assert (MU1 : munch [(SPV - 352, SPV)] m1 m2).
  { eapply munch_weaken; [|exact MU]. unfold sub_fp. intros x HX. cbn [outside] in HX |- *. destruct HX as (HX & _).
    split; [clear - HX; lia|]. split; [clear - HX HSTP SA; lia | exact I]. }
  assert (MU2 : munch [(SPV - 248, SPV - 160)] m1 m2).
  { eapply munch_weaken; [|exact MU]. unfold sub_fp. intros x HX. cbn [outside] in HX |- *. destruct HX as (HX & _).
    split; [clear - HX; lia|]. split; [clear - HX HSTP SA; lia | exact I]. }
  assert (FST2 : rw_cells usegs m2 (SPV + -208) (sa ++ [C8 (Z_to_bv 64 st); C8 (Z_to_bv 64 (T + 8))] ++ sb)).
  { apply rw_cells_app. split.
    { eapply rw_cells_transport; [exact FSA | exact MU | exact WM |]. cbn [disjoint_from].
      split; [clear - HSTP SA; lia | split; [clear - HSTP SA; lia | exact I]]. }
    apply rw_cells_app. split.
    { replace (SPV + -208 + Z.of_nat (cells_size sa)) with STP by (clear - HSTP; lia). exact STC2. }
    match goal with |- rw_cells _ _ ?A _ => replace A with (STP + 16) by (cbn [cells_size csize Nat.add]; clear - HSTP; lia) end.
    eapply rw_cells_transport; [exact FSB | exact MU | exact WM |]. cbn [disjoint_from].
    split; [clear - HSTP SA SAB; lia | split; [clear - HSTP SA SAB; lia | exact I]]. }
  pose proof (JOIN m2 _ _ MU2 WM BDC2 FST2 eq_refl (SS _ _)) as FR2.
  pose proof (TRANS m2 _ MU1 WM MI2 FR2) as INV2.
  eapply (K m2 t0' a1' a2' a3' a4' a5' a6' a7' cw' jpad' bc' ptr' st); [exact INV2 | | exact HST].
  unfold seqd_ibits. cbn [q_SEQ q_sq]. split; [clear - HBC; lia | exact HBP].
Qed.

(* [comment removed for export] *)
Lemma seqd_ifse_LL : forall P OEND LEND, seqd_static P OEND LEND -> ai_43c P OEND LEND -> ai_408 P OEND LEND.
Proof.
  intros P OEND LEND ST CONT. unfold ai_408.
  intros m1 c0 c8 c16 c48 c72 c80 c88 cw u144 u152 u160 u168 u176 u184 p0 p1 p2 jpad jseq bc ptr x5 x6 x7 x13 x14 x15 x16 x17 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 INV IB.
  unfold ai_43c in CONT.
  eapply (seqd_ifse_call P OEND LEND m1 c0 c8 c16 c48 c72 c80 c88 cw jpad bc ptr [] u144 u152 [C8 u160; C8 u168; C8 u176; C8 u184] p0 p1 p2 jseq K_LL (q_tLL P) (q_LLT P) (q_SPV P + -208) 64);
    [ exact ST | exact INV | left; repeat split; reflexivity | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia
    | cbn [cells_size csize Nat.add]; lia | exact IB | lia | ].
  intros m2 t0' a1' a2' a3' a4' a5' a6' a7' cw' jpad' bc' ptr' st INV2 IB2 HST.
  rewrite ret_pc_even by (first [reflexivity | lia]).
  eapply (CONT m2 c0 c8 c16 c48 c72 c80 c88 cw' u160 u168 u176 u184 p0 p1 p2 jpad' jseq bc' ptr' st); [exact INV2 | exact IB2 | exact HST].
Qed.

(* [comment removed for export] *)
Lemma seqd_ifse_OF : forall P OEND LEND, seqd_static P OEND LEND -> ai_56c P OEND LEND -> ai_538 P OEND LEND.
Proof.
  intros P OEND LEND ST CONT. unfold ai_538.
  intros m1 c0 c8 c16 c48 c72 c80 c88 cw u160 u168 u176 u184 p0 p1 p2 jpad jseq bc ptr sLL x5 x6 x7 x13 x14 x15 x16 x17 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 INV IB HLL.
  unfold ai_56c in CONT.
  eapply (seqd_ifse_call P OEND LEND m1 c0 c8 c16 c48 c72 c80 c88 cw jpad bc ptr [C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (q_LLT P + 8))] u160 u168 [C8 u176; C8 u184] p0 p1 p2 jseq K_OF (q_tOF P) (q_OFT P) (q_SPV P + -192) 73);
    [ exact ST | exact INV | right; left; repeat split; reflexivity | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia
    | cbn [cells_size csize Nat.add]; lia | exact IB | lia | ].
  intros m2 t0' a1' a2' a3' a4' a5' a6' a7' cw' jpad' bc' ptr' st INV2 IB2 HST.
  rewrite ret_pc_even by (first [reflexivity | lia]).
  eapply (CONT m2 c0 c8 c16 c48 c72 c80 c88 cw' u176 u184 p0 p1 p2 jpad' jseq bc' ptr' sLL st); [exact INV2 | exact IB2 | exact HLL | exact HST].
Qed.

(* [comment removed for export] *)
Lemma seqd_ifse_ML : forall P OEND LEND, seqd_static P OEND LEND -> ai_6a8 P OEND LEND -> ai_66c P OEND LEND.
Proof.
  intros P OEND LEND ST CONT. unfold ai_66c.
  intros m1 c0 c8 c16 c48 c72 c80 c88 cw u176 u184 p0 p1 p2 jpad jseq bc ptr sLL sOF x5 x6 x7 x13 x14 x15 x16 x17 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 INV IB HLL HOF.
  unfold ai_6a8 in CONT.
  eapply (seqd_ifse_call P OEND LEND m1 c0 c8 c16 c48 c72 c80 c88 cw jpad bc ptr [C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (q_LLT P + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (q_OFT P + 8))] u176 u184 [] p0 p1 p2 jseq K_ML (q_tML P) (q_MLT P) (q_SPV P + -176) 82);
    [ exact ST | exact INV | right; right; repeat split; reflexivity | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia
    | cbn [cells_size csize Nat.add]; lia | exact IB | lia | ].
  intros m2 t0' a1' a2' a3' a4' a5' a6' a7' cw' jpad' bc' ptr' st INV2 IB2 HST.
  rewrite ret_pc_even by (first [reflexivity | lia]).
  eapply (CONT m2 c0 c8 c16 c48 c72 c80 c88 cw' p0 p1 p2 jpad' jseq bc' ptr' sLL sOF st); [exact INV2 | exact IB2 | exact HLL | exact HOF | exact HST].
Qed.

(* [comment removed for export] *)
Lemma seqd_i7ac : forall P OEND LEND, seqd_static P OEND LEND -> at_head P OEND LEND (q_nbSeq P) -> ai_7ac P OEND LEND.
Proof.
  intros P OEND LEND ST CONT. unfold ai_7ac.
  intros m1 cw bc ptr sLL sOF sML p0 p1 p2 j0 jpad jseq x1 x5 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 INV IB HLL HOF HML.
  unfold at_head in CONT.
  assert (A1 : q_DST P <= q_DST P <= OEND /\ q_LITP P <= q_LITP P <= LEND).
  { clear - ST.
    destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
    cbn [seqd_static q_DST q_LITP] in *. sd_static_open ST. unfold held in S4, S8, S10. clear - S4 S8 S10. lia. }
  destruct A1 as (A1 & A2). destruct IB as (IB1 & IB2).
  assert (LF : seqd_lfacts P OEND LEND (100 + 100 * (q_nbSeq P - q_nbSeq P) + 0) (q_DST P) (q_LITP P) bc ptr sLL sOF sML).
  { unfold seqd_lfacts. split; [exact A1|]. split; [exact A2|]. split; [exact HLL|]. split; [exact HOF|]. split; [exact HML|].
    split; [clear - IB1; lia | exact IB2]. }
  exact (CONT m1 cw bc ptr sLL sOF sML p0 p1 p2 (q_LITP P) (q_DST P) x1 x5 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31
    (seqd_iinv_linv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) LF).
Qed.
