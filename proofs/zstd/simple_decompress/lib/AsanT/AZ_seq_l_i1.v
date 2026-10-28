(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_hkit AZ_seq_l_ibase AZ_seq_l_iat AZ_seq_l_ikit AZ_seq_inl_initfse_L1.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac kxa_norm ::= unfold shspan in *.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac kxl_hyp ::= lazymatch goal with |- ?G => first [ match goal with H : G |- _ => exact H end | match goal with H : rheld G |- _ => exact H end ] end.
Ltac kxa_rng ::= first [ kxl_hyp | kxa_rng0 ].
Ltac kxl_rng ::=
  first [ kxl_hyp
        | lazymatch goal with |- rng ?RNG ?A ?N => match goal with H : rng RNG ?A0 ?N0 |- _ => apply (rng_sub' RNG A0 N0 A N H); solve [kxl_lia_small] end end
        | kx_rng ].
(* [comment removed for export] *)
Ltac i1_hcut H k d H1 H2 :=
  lazymatch type of H with rw_cells ?sg ?mm ?A ?cs =>
    let pre := eval cbn [firstn] in (firstn k cs) in
    let post := eval cbn [skipn] in (skipn k cs) in
    change (rw_cells sg mm A (pre ++ post)) in H;
    apply rw_cells_app in H; destruct H as [H1 H2];
    change (rw_cells sg mm (A + d) post) in H2
  end.
Ltac i1_gcut k d :=
  lazymatch goal with |- rw_cells ?sg ?mm ?A ?cs =>
    let pre := eval cbn [firstn] in (firstn k cs) in
    let post := eval cbn [skipn] in (skipn k cs) in
    change (rw_cells sg mm A (pre ++ post)); apply rw_cells_app; split; [| change (rw_cells sg mm (A + d) post)]
  end.

Section CANSEC1. Context {rc : runConstT}.

Lemma sql_i1_ok : forall P OEND, sql_static P OEND (l_LITP P) (l_LBE P) (l_LOC P) ->
  (l_LLT P + 4104 < 2^47 /\ l_OFT P + 2056 < 2^47 /\ l_MLT P + 4104 < 2^47) ->
  ai_I3 P OEND -> ai_I1 P OEND.
Proof.
  intros P OEND ST TST CONT.
  unfold ai_I1. intros m1 ja jb jc jd je jf jg jh ji jr jseq jpad j72 p0 p1 p2 cw bc ptr x1 x5 x6 x7 x12 x14 x15 x17 x27 x28 x29 x30 INV HBC BOK.
  unfold ai_I3 in CONT.
  pose proof (sql_iasan_now _ _ _ _ _ _ _ _ ST INV) as AS.
  pose proof (sql_itbl_asan _ _ _ _ _ _ _ _ ST INV) as (ATLL & ATOF & _).
  pose proof (sql_itbl_logs _ _ _ _ _ _ _ _ ST INV) as (_ & _ & _ & TLG & TOG & _).
  pose proof (sql_iinv_frame _ _ _ _ _ _ _ _ ST INV) as TRANS.
  pose proof INV as (_ & _ & _ & TLL & _).
  apply (sql_iopen_k _ _ _ _ _ _ _ _ ST INV); intros FR FRF PT SQB MI UFL USQ RSQ RSQS UD RD RDS.
  clear INV.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  cbn [sql_ifrB sql_iffB sql_iffC sql_iregsB sql_asan app l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in *.
  pose proof ST as ST0. sd_static_open ST0. try unfold held in *.
  destruct S61 as (ASTK & _ & _ & _ & ED8 & _ & FRBM & _ & _ & FFc & ESHF & RFF & RSHF & _).
  destruct S63 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ABFF).
  destruct ASTK as (_ & RLO & _).
  destruct AS as (_ & _ & _ & _ & ACL & _ & _ & _ & AZS & ART).
  assert (LN : Z.of_nat (length (map (Z_to_bv 8) sq)) = zlen sq) by (rewrite length_map; reflexivity).
  assert (PL9 : 1 <= 2 ^ st_log tLL <= 512) by (clear - TLG; split; [pose proof (Z.pow_pos_nonneg 2 (st_log tLL)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
  assert (PO1 : 1 <= 2 ^ st_log tOF) by (clear - TOG; pose proof (Z.pow_pos_nonneg 2 (st_log tOF)); lia).
  assert (FF4096 : 4096 <= FF) by (clear - S49; lia).
  assert (G : 4096 <= FF + 32 /\ FF + 32 + 56 < 2^47 /\ 4096 <= LLT /\ LLT + 8 * (1 + 2 ^ st_log tLL) < 2^47 /\ 4096 <= SEQ /\
              SEQ + Z.of_nat (length (map (Z_to_bv 8) sq)) < 2^47 /\ 1 <= Z.of_nat (length (map (Z_to_bv 8) sq)) /\ 4096 <= FRB /\ FRB + 296 < 2^47 /\
              4096 <= DCTX /\ DCTX + 24 < 2^47 /\ 4096 <= OFT /\ OFT + 8 < 2^47)
    by (rewrite LN; clear - S13 S14 S15 S17 S18 S19 S20 S21 S22 S47 S50 FF4096 PL9 TST; lia).
  destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
  assert (M1 : (FF + 32) mod 8 = 0) by (clear - FFc; Z.div_mod_to_equations; lia).
  assert (M2 : LLT mod 4 = 0) by (clear - S44; Z.div_mod_to_equations; lia).
  assert (M3 : FRB mod 8 = 0) by (clear - FRBM; Z.div_mod_to_equations; lia).
  assert (M4 : DCTX mod 8 = 0) by (clear - ED8; rewrite ED8; Z.div_mod_to_equations; lia).
  assert (M5 : OFT mod 4 = 0) by (clear - S45; Z.div_mod_to_equations; lia).
  assert (DJ1 : FF + 32 + 56 <= SEQ \/ SEQ + Z.of_nat (length (map (Z_to_bv 8) sq)) <= FF + 32) by (rewrite LN; clear - S56; lia).
  assert (DJ2 : FF + 32 + 56 <= LLT \/ LLT + 8 * (1 + 2 ^ st_log tLL) <= FF + 32) by (clear - S58 PL9; lia).
  assert (DJ3 : FF + 32 + 56 <= FRB + 288 \/ FRB + 296 <= FF + 32) by (clear - S50 S18 S47; lia).
  assert (DJ4 : FRB + 296 <= SEQ \/ SEQ + Z.of_nat (length (map (Z_to_bv 8) sq)) <= FRB + 288) by (rewrite LN; clear - S25 S18 S47; lia).
  assert (DJ5 : FRB + 296 <= LLT \/ LLT + 8 * (1 + 2 ^ st_log tLL) <= FRB + 288) by (clear - S28 S18 S47 PL9; lia).
  assert (DJ6 : FF + 32 + 56 <= DCTX + 16 \/ DCTX + 24 <= FF + 32) by (clear - S54; lia).
  assert (DJ7 : FRB + 296 <= DCTX + 16 \/ DCTX + 24 <= FRB + 288) by (clear - S27 S18 S47; lia).
  (* [comment removed for export] *)
  unfold dctx_ptrs in PT.
  i1_hcut PT 2%nat 16 PT1 PT2.
  i1_hcut PT2 1%nat 8 PT3 PT4.
  i1_hcut FRF 1%nat 32 FA FR1.
  i1_hcut FR1 6%nat 40 FB FR2.
  destruct (sql_cbst48 m1 _ [] j72 _ FR2) as (w1 & w2 & j' & FR3). cbn [app] in FR3.
  i1_hcut FR3 2%nat 16 FC FD.
  i1_hcut FR 25%nat 272 FRP FRR.
  i1_hcut FRR 1%nat 32 FRM FRS.
  apply (rw_cells_split_CB bsegs m1 (FRB + 272) [] 32 jh [] [16; 8; 8]%nat) in FRM; [| reflexivity].
  cbn [app mk_CB_cells] in FRM.
  i1_hcut FRM 1%nat 16 FRM16 FRM2.
  destruct (cb8_as_c8 bsegs m1 _ [] _ _ FRM2) as [c288 FRM3]. cbn [app] in FRM3.
  i1_hcut FRM3 1%nat 8 FRC FRK.
  replace (FRB + 272 + 16) with (FRB + 288) in FRC by (clear; lia).
  assert (ABD : app_blk (FF + 32) (FF + 32 + 40)) by (eapply app_blk_sub; [apply ablk_app_blk; [exact ABFF | clear; lia] | clear; lia | clear; lia | clear; lia]).
  assert (ABS : app_blk (FF + 32 + 40) (FF + 32 + 56)) by (eapply app_blk_sub; [apply ablk_app_blk; [exact ABFF | clear; lia] | clear; lia | clear; lia | clear; lia]).
  assert (AOBD : aro RNG m1 (FF + 32) 40).
  { split; [eapply unpoisoned_sub; [exact UFL | clear; lia | clear; lia]|].
    split; [eapply rng_sub; [exact RFF | clear; lia | clear; lia]|].
    eapply rng_sub; [exact RSHF | |]; rewrite ESHF; unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - S51; Z.div_mod_to_equations; lia. }
  assert (AOST : aro RNG m1 (FF + 32 + 40) 16).
  { split; [eapply unpoisoned_sub; [exact UFL | clear; lia | clear; lia]|].
    split; [eapply rng_sub; [exact RFF | clear; lia | clear; lia]|].
    eapply rng_sub; [exact RSHF | |]; rewrite ESHF; unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - S51; Z.div_mod_to_equations; lia. }
  assert (APF : app_blk (FRB + 288) (FRB + 296)).
  { replace (FRB + 296) with (FRB + 288 + 8) by (clear; lia). eapply azstk_app; [exact AZS | clear - S18 S47; lia | clear; lia | clear - S47; lia]. }
  assert (RGF : rng RNG (FRB + 288) 8) by (eapply rng_sub; [exact RLO | clear - S18 S47; lia | clear - S47; lia]).
  assert (AROD : aro RNG m1 (DCTX + 16) 8) by (eapply aro_sub; [exact (conj UD (conj RD RDS)) | clear; lia | clear; lia | clear; unfold DCTX_SIZEOF; lia]).
  assert (ARON : aro RNG m1 OFT 8) by (eapply aro_sub; [exact ATOF | clear; lia | clear; lia | clear - PO1; lia]).
  assert (AROS : aro RNG m1 SEQ (Z.of_nat (length (map (Z_to_bv 8) sq)))) by (rewrite LN; exact (conj USQ (conj RSQ RSQS))).
  assert (IB : bit_okS SEQ (Z.of_nat (length (map (Z_to_bv 8) sq))) bc ptr) by (unfold bit_okS; rewrite LN; exact BOK).
  (* [comment removed for export] *)
  pose proof sq_inl_initfse_L1_proof as W. unfold sq_inl_initfse_L1_stmt, sq_inl_initfse_L1_stmt_if in W.
  eapply evtF_cut.
  { eapply (W RNG x1 (Z_to_bv 64 FRB) gp tp x5 x6 x7 (Z_to_bv 64 SPV) x12 x14 x15 p0 x17 (Z_to_bv 64 CAP) (Z_to_bv 64 SHF)
              (Z_to_bv 64 nbSeq) (Z_to_bv 64 FF) (Z_to_bv 64 LBE) x27 x28 x29 x30 _ F fc m1 FRB (FF + 32) LLT SEQ 64 bc ptr DCTX OFT
              cw w1 w2 c288 jpad (map (Z_to_bv 8) sq) K_LL tLL);
      [ exact FB | exact FC | exact FRC | exact PT3 | exact TLL | exact OKLL | exact SQB
      | exact G1 | exact G2 | exact G3 | exact G4 | exact G5 | exact G6 | exact G7 | exact G8 | exact G9 | exact G10 | exact G11 | exact G12 | exact G13
      | exact M1 | exact M2 | exact M3 | exact M4 | exact M5
      | exact DJ1 | exact DJ2 | exact DJ3 | exact DJ4 | exact DJ5 | exact DJ6 | exact DJ7
      | clear - HBC; lia | clear; lia | exact IB
      | exact ABD | exact AOBD | exact ABS | exact AOST | exact APF | exact RGF | exact AROD | exact ARON | exact AROS | exact ATLL
      | exact ACL | exact ART | exact MI | exact I ]. }
  intros ms' PO. unfold sq_inl_initfse_L1_post in PO.
  destruct PO as (y0 & y1 & y2 & a0' & a1' & a2' & a3' & a4' & a5' & a7' & m' & cw' & bc' & jpad' & ptr' & st' & -> & MU & WM & MI' & HBD' & HST' & H288' & E1 & E2 & E3 & E4 & E5 & STB & BCB & BOK').
  subst y1 y2 a0' a1' a3'.
  assert (MUL : munch [(FRB, FRB + 568); (FF, FF + 256)] m1 m').
  { eapply munch_weaken; [|exact MU]. unfold sub_fp. intros z Hz. cbn [outside] in Hz |- *. clear - Hz; lia. }
  pose proof (rw_cells_transport bsegs _ _ _ _ _ FA MU WM) as FA'.
  specialize (FA' ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; clear - S47 S18 S50; lia)).
  pose proof (rw_cells_transport bsegs _ _ _ _ _ FD MU WM) as FD'.
  specialize (FD' ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; clear - S47 S18 S50; lia)).
  pose proof (rw_cells_transport bsegs _ _ _ _ _ FRP MU WM) as FRP'.
  specialize (FRP' ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; clear - S47 S18 S50; lia)).
  pose proof (rw_cells_transport bsegs _ _ _ _ _ FRM16 MU WM) as FRM16'.
  specialize (FRM16' ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; clear - S47 S18 S50; lia)).
  pose proof (rw_cells_transport bsegs _ _ _ _ _ FRK MU WM) as FRK'.
  specialize (FRK' ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; clear - S47 S18 S50; lia)).
  pose proof (rw_cells_transport bsegs _ _ _ _ _ FRS MU WM) as FRS'.
  specialize (FRS' ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; clear - S47 S18 S50; lia)).
  replace (FRB + 288) with (FRB + 272 + 16) in H288' by (clear; lia).
  replace (FRB + 272 + 32) with (FRB + 272 + 16 + 8 + 8) in FRS' by (clear; lia).
  eapply (CONT m' ja jb jc jd je jf jg (firstn 16 jh) (firstn 8 (skipn 8 (skipn 16 jh))) ji jr jseq jpad' j' p0 p1 p2 cw' bc' ptr' st'
            x1 y0 a2' a4' a5' a7' x27 x28 x29 x30).
  - eapply TRANS; [exact MUL | exact WM | exact MI' | |].
    + i1_gcut 25%nat 272; [exact FRP'|].
      i1_gcut 1%nat 16; [exact FRM16'|].
      i1_gcut 1%nat 8; [exact H288'|].
      i1_gcut 1%nat 8; [exact FRK'|].
      exact FRS'.
    + i1_gcut 1%nat 32; [exact FA'|].
      i1_gcut 6%nat 40; [exact HBD'|].
      i1_gcut 2%nat 16; [exact HST'|].
      exact FD'.
  - clear - BCB; lia.
  - unfold bit_ok. unfold bit_okS in BOK'. rewrite LN in BOK'. exact BOK'.
  - exact STB.
Qed.

End CANSEC1.
