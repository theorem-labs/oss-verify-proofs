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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_hkit AZ_seq_l_ibase AZ_seq_l_iat AZ_seq_l_ikit AZ_seq_inl_initfse_L3.
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

Ltac lg5_cut H n AT H1 H2 :=
  lazymatch type of H with rw_cells ?sg ?mm ?A ?cs =>
    let pre := eval cbn [firstn] in (firstn n cs) in
    let post := eval cbn [skipn] in (skipn n cs) in
    change (rw_cells sg mm A (pre ++ post)) in H;
    apply rw_cells_app in H; destruct H as [H1 H2];
    let k0 := eval cbv [cells_size csize Nat.add] in (cells_size pre) in
    let k := eval cbv in (Z.of_nat k0) in
    change (rw_cells sg mm (A + k) post) in H2;
    replace (A + k) with AT in H2 by (clear; lia)
  end.
Ltac lg5_gcut n :=
  lazymatch goal with |- rw_cells ?sg ?mm ?A ?cs =>
    let pre := eval cbn [firstn] in (firstn n cs) in
    let post := eval cbn [skipn] in (skipn n cs) in
    change (rw_cells sg mm A (pre ++ post)); apply rw_cells_app; split
  end.

Section CANSEC1. Context {rc : runConstT}.

Lemma sql_i5_ok : forall P OEND, sql_static P OEND (l_LITP P) (l_LBE P) (l_LOC P) ->
  (l_LLT P + 4104 < 2^47 /\ l_OFT P + 2056 < 2^47 /\ l_MLT P + 4104 < 2^47) ->
  ai_I7 P OEND -> ai_I5 P OEND.
Proof.
  intros P OEND ST TST CONT.
  unfold ai_I5.
  intros m1 ja jb jc jd je jf jg jh jk ji jr jseq jpad j104 p0 p1 p2 cw bc ptr sLL sOF x1 x7 x12 x13 x14 x15 x17 x27 x29 INV HBC BOK HS1 HS2.
  pose proof (sql_iinv_mi _ _ _ _ _ _ _ _ INV) as MI.
  pose proof (sql_iasan_now _ _ _ _ _ _ _ _ ST INV) as ASN.
  pose proof (sql_itbl_asan _ _ _ _ _ _ _ _ ST INV) as (_ & _ & ATM).
  apply (sql_iopen_k _ _ _ _ _ _ _ _ ST INV); intros FR0 FF0 _ SQB _ UFL _ _ _ _ _ _.
  pose proof INV as (_ & _ & _ & _ & _ & TBM & _).
  pose proof ST as ST0. pose proof INV as INV0. clear INV.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  cbv delta [ai_I7 sql_ifrB sql_iffD sql_ffr sql_iregsB] in *.
  cbn [app l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in *.
  sd_static_open ST. try unfold held in *.
  destruct S61 as (ASTK & _ & _ & _ & _ & _ & _ & _ & _ & _ & ESHF & RFF & RSHF & _).
  destruct S63 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ABFF).
  destruct ASN as (_ & _ & ASQ & _ & ACL & _ & _ & _ & AZS & ART).
  destruct ASTK as (KH & RST & _).
  destruct AZS as (RLO & RHI & _ & _ & _ & ABS & _).
  assert (LN : Z.of_nat (length (map (Z_to_bv 8) sq)) = zlen sq) by (rewrite length_map; reflexivity).
  assert (FF4096 : 4096 <= FF) by (clear - S49; lia).
  assert (PM9 : 1 <= 2 ^ st_log tML <= 512).
  { pose proof (proj1 OKML) as TRK. cbn [kind_maxLog] in TRK. clear - TRK.
    pose proof (Z.pow_le_mono_r 2 (st_log tML) 9) as PM. pose proof (Z.pow_pos_nonneg 2 (st_log tML)) as PP.
    set (EE := 2 ^ st_log tML) in *. clearbody EE. change (2 ^ 9) with 512 in PM. lia. }
  assert (KHF : KHIGH <= FRB) by (clear - KH S18 S47; lia).
  assert (DJ1 : FF + 32 + 88 <= SEQ \/ SEQ + Z.of_nat (length (map (Z_to_bv 8) sq)) <= FF + 32) by (rewrite LN; clear - S56; lia).
  assert (DJ2 : FF + 32 + 88 <= MLT \/ MLT + 8 * (1 + 2 ^ st_log tML) <= FF + 32) by (clear - S60 PM9; lia).
  assert (DJ3 : FF + 32 + 88 <= FRB + 136 \/ FRB + 304 <= FF + 32) by (clear - S50 S18 S47; lia).
  assert (DJ4 : FRB + 304 <= SEQ \/ SEQ + Z.of_nat (length (map (Z_to_bv 8) sq)) <= FRB + 136) by (rewrite LN; clear - S25 S18 S47; lia).
  assert (DJ5 : FRB + 304 <= MLT \/ MLT + 8 * (1 + 2 ^ st_log tML) <= FRB + 136) by (clear - S30 S18 S47 PM9; lia).
  assert (M1 : (FF + 32) mod 8 = 0) by (clear - S51; Z.div_mod_to_equations; lia).
  assert (M2 : MLT mod 4 = 0) by (clear - S46; Z.div_mod_to_equations; lia).
  assert (M3 : FRB mod 8 = 0) by (clear - S48; Z.div_mod_to_equations; lia).
  assert (IB : bit_okS SEQ (Z.of_nat (length (map (Z_to_bv 8) sq))) bc ptr) by (unfold bit_okS; rewrite LN; exact BOK).
  assert (ABD : app_blk (FF + 32) (FF + 32 + 40)).
  { eapply app_blk_sub; [apply ablk_app_blk; [exact ABFF | clear; lia] | clear; lia | clear; lia | clear; lia]. }
  assert (ABS2 : app_blk (FF + 32 + 72) (FF + 32 + 88)).
  { eapply app_blk_sub; [apply ablk_app_blk; [exact ABFF | clear; lia] | clear; lia | clear; lia | clear; lia]. }
  assert (AOBD : aro RNG m1 (FF + 32) 40).
  { split; [eapply unpoisoned_sub; [exact UFL | clear; lia | clear; lia]|].
    split; [eapply rng_sub; [exact RFF | clear; lia | clear; lia]|].
    eapply rng_sub; [exact RSHF | |]; rewrite ESHF; unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - S51; Z.div_mod_to_equations; lia. }
  assert (AOST : aro RNG m1 (FF + 32 + 72) 16).
  { split; [eapply unpoisoned_sub; [exact UFL | clear; lia | clear; lia]|].
    split; [eapply rng_sub; [exact RFF | clear; lia | clear; lia]|].
    eapply rng_sub; [exact RSHF | |]; rewrite ESHF; unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - S51; Z.div_mod_to_equations; lia. }
  assert (AOSQ : aro RNG m1 SEQ (Z.of_nat (length (map (Z_to_bv 8) sq)))).
  { rewrite LN. apply aregU_aro. apply ASQ. clear - S15; lia. }
  assert (AF136 : app_blk (FRB + 136) (FRB + 152)) by (eapply app_blk_sub; [exact ABS | clear - S18 S47; lia | clear; lia | clear - S47; lia]).
  assert (AF176 : app_blk (FRB + 176) (FRB + 208)) by (eapply app_blk_sub; [exact ABS | clear - S18 S47; lia | clear; lia | clear - S47; lia]).
  assert (AF272 : app_blk (FRB + 272) (FRB + 280)) by (eapply app_blk_sub; [exact ABS | clear - S18 S47; lia | clear; lia | clear - S47; lia]).
  assert (AF296 : app_blk (FRB + 296) (FRB + 304)) by (eapply app_blk_sub; [exact ABS | clear - S18 S47; lia | clear; lia | clear - S47; lia]).
  assert (RG136 : rng RNG (FRB + 136) 16) by (eapply rng_sub; [exact RST | clear - S18 S47; lia | clear - S18 S47; lia]).
  assert (RG176 : rng RNG (FRB + 176) 32) by (eapply rng_sub; [exact RST | clear - S18 S47; lia | clear - S18 S47; lia]).
  assert (RG224 : rng RNG (FRB + 224) 16) by (eapply rng_sub; [exact RST | clear - S18 S47; lia | clear - S18 S47; lia]).
  assert (RG272 : rng RNG (FRB + 272) 8) by (eapply rng_sub; [exact RST | clear - S18 S47; lia | clear - S18 S47; lia]).
  assert (RG296 : rng RNG (FRB + 296) 8) by (eapply rng_sub; [exact RST | clear - S18 S47; lia | clear - S18 S47; lia]).
  (* [comment removed for export] *)
  lg5_cut FF0 1%nat (FF + 32) FA FF1.
  lg5_cut FF1 6%nat (FF + 72) FB FF2.
  lg5_cut FF2 4%nat (FF + 32 + 72) FM FF3.
  lg5_cut FF3 1%nat (FF + 120) FS FD.
  destruct (sql_cb16_words m1 (FF + 32 + 72) [] j104 [] FS) as (st0 & tb0 & FS2).
  lg5_cut FR0 14%nat (FRB + 136) RA R1.
  lg5_cut R1 1%nat (FRB + 152) RB R2.
  lg5_cut R2 3%nat (FRB + 176) RC R3.
  lg5_cut R3 1%nat (FRB + 224) RD R4.
  lg5_cut R4 2%nat (FRB + 240) RE R5.
  lg5_cut R5 4%nat (FRB + 272) RF R6.
  lg5_cut R6 1%nat (FRB + 280) RG R7.
  lg5_cut R7 2%nat (FRB + 296) RH R8.
  lg5_cut R8 1%nat (FRB + 304) RI RJ.
  destruct (sql_cb16_words m1 (FRB + 136) [] je [] RB) as (c136 & c144 & RB2).
  destruct (sql_cbst48 m1 (FRB + 176) [] jf [] RD) as (w1 & w2 & jf1 & RD1).
  destruct (sql_cbst32 m1 (FRB + 176) [C8 w1; C8 w2] jf1 [] RD1) as (w3 & w4 & jf2 & RD2).
  cbn [app] in RD2.
  lg5_cut RD2 4%nat (FRB + 208) RD4 RD5.
  destruct (sql_cb8_word m1 (FRB + 272) [] jh [] RG) as (c272 & RG2).
  destruct (sql_cb8_word m1 (FRB + 296) [] jk [] RI) as (c296 & RI2).
  (* [comment removed for export] *)
  pose proof sq_inl_initfse_L3_proof as W. unfold sq_inl_initfse_L3_stmt, sq_inl_initfse_L3_stmt_if in W.
  eapply evtF_cut.
  { eapply (W RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 FRB (FF + 32) MLT SEQ 82 bc ptr DCTX nbSeq PFX DST
              cw st0 tb0 c136 c144 w1 w2 w3 w4 c272 c296 jpad (map (Z_to_bv 8) sq) K_ML tML).
    all: first [ exact I | eassumption
               | (try rewrite LN); clear - FF4096 S1 S2 S3 S4 S5 S6 S7 S13 S14 S15 S16 S17 S18 S19 S20 S23 S47 S50 TST PM9 HBC; lia ]. }
  intros ms' PO. unfold sq_inl_initfse_L3_post in PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y7 & y27 & y29 & y30 & m' & cw' & bc' & jpad' & ptr' & st' & -> & MU & WM & MI' & HBD' & HST' & H136 & H176 & H272 & H296 & E0 & E1 & E27 & E29 & E30 & STB & BCB & BOK').
  subst y0 y1 y27 y29 y30.
  pose proof (rw_cells_transport bsegs _ _ _ _ _ FA MU WM) as FA'.
  specialize (FA' ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; clear - S47 S18 S50; lia)).
  pose proof (rw_cells_transport bsegs _ _ _ _ _ FM MU WM) as FM'.
  specialize (FM' ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; clear - S47 S18 S50; lia)).
  pose proof (rw_cells_transport bsegs _ _ _ _ _ FD MU WM) as FD'.
  specialize (FD' ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; clear - S47 S18 S50; lia)).
  pose proof (rw_cells_transport bsegs _ _ _ _ _ RA MU WM) as RA'.
  specialize (RA' ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; clear - S47 S18 S50; lia)).
  pose proof (rw_cells_transport bsegs _ _ _ _ _ RC MU WM) as RC'.
  specialize (RC' ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; clear - S47 S18 S50; lia)).
  pose proof (rw_cells_transport bsegs _ _ _ _ _ RD5 MU WM) as RD5'.
  specialize (RD5' ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; clear - S47 S18 S50; lia)).
  pose proof (rw_cells_transport bsegs _ _ _ _ _ RE MU WM) as RE'.
  specialize (RE' ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; clear - S47 S18 S50; lia)).
  pose proof (rw_cells_transport bsegs _ _ _ _ _ RF MU WM) as RF'.
  specialize (RF' ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; clear - S47 S18 S50; lia)).
  pose proof (rw_cells_transport bsegs _ _ _ _ _ RH MU WM) as RH'.
  specialize (RH' ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; clear - S47 S18 S50; lia)).
  pose proof (rw_cells_transport bsegs _ _ _ _ _ RJ MU WM) as RJ'.
  specialize (RJ' ltac:(cbn [disjoint_from cells_size csize Nat.add]; repeat split; clear - S47 S18 S50; lia)).
  replace (FF + 32 + 72) with (FF + 104) in HST' by (clear; lia).
  assert (MUL : munch [(FRB, FRB + 568); (FF, FF + 256)] m1 m').
  { eapply munch_weaken; [|exact MU]. unfold sub_fp. intros z Hz. cbn [outside] in Hz |- *. destruct Hz as (Hz1 & Hz2 & _). repeat split; clear - Hz1 Hz2; lia. }
  (* [comment removed for export] *)
  apply (CONT m' ja jb jc jd jf2 jg ji jr jseq jpad' p0 p1 p2 cw' bc' ptr' sLL sOF st' x1 (Z_to_bv 64 SBITMASK) x7 (Z_to_bv 64 DST) y2 y3 y4 y5 y7 (Z_to_bv 64 (MLT + 8))).
  - eapply (sql_iinv_frame _ OEND _ _ _ m1 _ _ ST0 INV0 m' _ _ MUL WM MI').
    + cbn [l_FRB].
      lg5_gcut 34%nat; [| exact RJ'].
      lg5_gcut 33%nat; [| exact H296].
      lg5_gcut 31%nat; [| exact RH'].
      lg5_gcut 30%nat; [| exact H272].
      lg5_gcut 26%nat; [| exact RF'].
      lg5_gcut 24%nat; [| exact RE'].
      lg5_gcut 23%nat; [| exact RD5'].
      lg5_gcut 19%nat; [| exact H176].
      lg5_gcut 16%nat; [| exact RC'].
      lg5_gcut 14%nat; [exact RA' | exact H136].
    + cbn [l_FF].
      lg5_gcut 13%nat; [| exact FD'].
      lg5_gcut 11%nat; [| exact HST'].
      lg5_gcut 7%nat; [| exact FM'].
      lg5_gcut 1%nat; [exact FA' | exact HBD'].
  - clear - BCB; lia.
  - unfold bit_ok. unfold bit_okS in BOK'. rewrite LN in BOK'. exact BOK'.
  - exact HS1.
  - exact HS2.
  - exact STB.
Qed.

End CANSEC1.
