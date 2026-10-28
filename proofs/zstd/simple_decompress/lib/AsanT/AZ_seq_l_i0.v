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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_hkit AZ_seq_l_ibase AZ_seq_l_iat AZ_seq_l_ikit AZ_seq_l_fin AZ_seq_inl_bitinit_L1.
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
Ltac i0_split H k sizes :=
  lazymatch type of H with rw_cells ?sg ?mm ?A ?cs =>
    let pre := eval cbn [firstn] in (firstn k cs) in
    lazymatch eval cbn [skipn] in (skipn k cs) with
    | CB ?n ?j :: ?post =>
        change (rw_cells sg mm A (pre ++ CB n j :: post)) in H;
        apply (rw_cells_split_CB sg mm A pre n j post sizes) in H; [| reflexivity];
        cbn [mk_CB_cells app] in H
    end
  end.
Ltac i0_cut H k R :=
  lazymatch type of H with rw_cells ?sg ?mm ?A ?cs =>
    let pre := eval cbn [firstn] in (firstn k cs) in
    let post := eval cbn [skipn] in (skipn k cs) in
    let n := eval vm_compute in (Z.of_nat (cells_size pre)) in
    change (rw_cells sg mm A (pre ++ post)) in H;
    apply rw_cells_app in H; destruct H as [H R];
    change (rw_cells sg mm (A + n) post) in R
  end.
Ltac i0_glue H R :=
  lazymatch type of H with rw_cells ?sg ?mm ?A ?pre =>
  lazymatch type of R with rw_cells _ _ _ ?post =>
    let G := fresh "G" in
    assert (G : rw_cells sg mm A (pre ++ post)) by (apply rw_cells_app; split; [exact H | exact R]);
    clear H R; rename G into H; cbn [app] in H
  end end.
Ltac i0_c8 H :=
  let w := fresh "w" in let H' := fresh "C" in
  lazymatch type of H with rw_cells ?sg ?mm ?A [CB 8 ?j] =>
    destruct (cb8_as_c8 sg mm A [] j [] H) as [w H']; clear H; rename H' into H; cbn [app] in H end.
Ltac i0_tr H MU WM D :=
  eapply (rw_cells_transport bsegs) in H;
    [| exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; repeat split; clear - D; lia].
Ltac i0_mul MU :=
  eapply munch_weaken; [|exact MU]; unfold sub_fp; let z := fresh "z" in let Hz := fresh "Hz" in
  intros z Hz; cbn [outside] in Hz |- *; destruct Hz as (Z1 & Z2 & _); repeat split; clear - Z1 Z2; lia.

Section CANSEC1. Context {rc : runConstT}.

Lemma sql_i0_ok : forall P OEND, sql_static P OEND (l_LITP P) (l_LBE P) (l_LOC P) ->
  sql_at_ierr P OEND -> ai_I1 P OEND -> ai_I0 P OEND.
Proof.
  intros P OEND ST IERR CONT.
  unfold ai_I0. intros m1 ja jb jc jd je jf jg jh jseq jbd j72 p0 p1 p2 x1 x5 x6 x7 x17 x28 x29 x30 INV.
  pose proof (sql_iinv_frame _ _ _ _ _ _ _ _ ST INV) as TRANS.
  pose proof (sql_iasan_now _ _ _ _ _ _ _ _ ST INV) as AS.
  pose proof (sql_itbl_asan _ _ _ _ _ _ _ _ ST INV) as (ATL & _ & _).
  apply (sql_iopen_k _ _ _ _ _ _ _ _ ST INV); intros FR FRF PT SQB MI UFL USQ RSQ RSQS UD RD RDS.
  apply (sql_rg_k _ _ _ _ _ ST); intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  clear INV.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  cbv delta [ai_I1 sql_iregsB sql_ifrB sql_iffB] in CONT. unfold sql_at_ierr in IERR.
  cbn [app sql_asan l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in *.
  sd_static_open ST. try unfold held in *.
  cbn [sql_astat sql_pro] in S61, S63.
  destruct S61 as (ASTK & _ & _ & _ & ED8 & _ & _ & _ & _ & _ & ESHF & _).
  destruct ASTK as (_ & _ & RAI).
  destruct S63 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ABFF).
  destruct AS as (_ & _ & _ & _ & _ & _ & _ & _ & AZS & ART).
  assert (LN : Z.of_nat (length (map (Z_to_bv 8) sq)) = zlen sq) by (rewrite length_map; reflexivity).
  assert (G1 : 4096 <= FF + 32) by (clear - RGA2 S49; lia).
  assert (G2 : FF + 32 + 40 < 2^47) by (clear - S50 S18 S17; lia).
  assert (G3 : SEQ + Z.of_nat (length (map (Z_to_bv 8) sq)) < 2^47) by (rewrite LN; clear - S14; lia).
  assert (G4 : 4096 <= FRB) by (clear - RGA1; lia).
  assert (G5 : FRB + 112 < 2^47) by (clear - RGA6 S17; lia).
  assert (G6 : DCTX + 8 < 2^47) by (clear - S20; lia).
  assert (G7 : 4096 <= LLT) by (clear - S21; lia).
  assert (G8 : LLT + 8 < 2^47) by (clear - S21; lia).
  assert (G9 : (FF + 32) mod 8 = 0) by (clear - RGC2; Z.div_mod_to_equations; lia).
  assert (G10 : FRB mod 8 = 0) by (clear - S48; Z.div_mod_to_equations; lia).
  assert (G11 : DCTX mod 8 = 0) by (clear - ED8; Z.div_mod_to_equations; lia).
  assert (G12 : LLT mod 4 = 0) by (clear - S44; Z.div_mod_to_equations; lia).
  assert (G13 : FF + 32 + 40 <= FRB + 32 \/ FRB + 112 <= FF + 32) by (clear - RGA8; lia).
  assert (G14 : 1 <= Z.of_nat (length (map (Z_to_bv 8) sq)) ->
                FF + 32 + 40 <= SEQ \/ SEQ + Z.of_nat (length (map (Z_to_bv 8) sq)) <= FF + 32)
    by (rewrite LN; clear - S56; lia).
  assert (G15 : 1 <= Z.of_nat (length (map (Z_to_bv 8) sq)) ->
                FRB + 112 <= SEQ \/ SEQ + Z.of_nat (length (map (Z_to_bv 8) sq)) <= FRB + 32)
    by (rewrite LN; clear - S25 RGA5 RGA6; lia).
  assert (G16 : FF + 32 + 40 <= DCTX \/ DCTX + 8 <= FF + 32) by (clear - S54; lia).
  assert (G17 : FRB + 112 <= DCTX \/ DCTX + 8 <= FRB + 32) by (clear - S27 RGA5 RGA6; lia).
  assert (ABD : app_blk (FF + 32) (FF + 32 + 40)).
  { eapply app_blk_sub; [apply ablk_app_blk; [exact ABFF | clear; lia] | clear; lia | clear; lia | clear; lia]. }
  assert (AOBD : aro RNG m1 (FF + 32) 40).
  { eapply (aro_sub _ _ (FF + 32) 112); [| clear; lia | clear; lia | clear; lia].
    split; [exact UFL|].
    split; [eapply rng_sub; [exact RFF | clear; lia | clear; lia]|].
    eapply rng_sub; [exact RSHF | |]; rewrite ESHF; unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - S51; Z.div_mod_to_equations; lia. }
  assert (AFR : app_blk (FRB + 32) (FRB + 112)).
  { replace (FRB + 112) with (FRB + 32 + 80) by (clear; lia).
    eapply azstk_app; [exact AZS | clear - RGA5; lia | clear; lia | clear - RGA6; lia]. }
  assert (RFR : rng RNG (FRB + 32) 80) by (eapply rng_sub; [exact RSTK | clear - RGA5; lia | clear - RGA6; lia]).
  assert (AOD : aro RNG m1 DCTX 8).
  { eapply aro_sub; [split; [exact UD | split; [exact RD | exact RDS]] | clear; lia | clear; lia | unfold DCTX_SIZEOF; clear; lia]. }
  assert (AOL : aro RNG m1 LLT 8).
  { pose proof (Z.pow_nonneg 2 (st_log tLL) ltac:(lia)) as HP. eapply aro_sub; [exact ATL | clear; lia | clear; lia | clear - HP; lia]. }
  assert (AOS : 1 <= Z.of_nat (length (map (Z_to_bv 8) sq)) -> aro RNG m1 SEQ (Z.of_nat (length (map (Z_to_bv 8) sq)))).
  { intros _. rewrite LN. split; [exact USQ | split; [exact RSQ | exact RSQS]]. }
  unfold dctx_ptrs in PT. i0_cut PT 1%nat PT2. clear PT2.
  i0_split FR 1%nat [24; 8; 16; 8; 8]%nat. i0_split FR 9%nat [8; 8; 8]%nat.
  i0_cut FR 11%nat R112. i0_cut FR 10%nat R104. i0_cut FR 6%nat R72. i0_cut FR 5%nat R64.
  i0_cut FR 4%nat R56. i0_cut FR 3%nat R40. i0_cut FR 2%nat R32.
  i0_c8 R32. i0_c8 R56. i0_c8 R64. i0_c8 R104.
  i0_cut FRF 2%nat F72. i0_cut FRF 1%nat F32.
  pose proof sq_inl_bitinit_L1_proof as W. unfold sq_inl_bitinit_L1_stmt, sq_inl_bitinit_L1_stmt_if in W.
  rewrite <- LN. change (Z_to_bv 64 2147450880) with (Z_to_bv 64 ASHOFF).
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply W with (m := m1) (FRB := FRB) (BD := FF + 32) (SEQ := SEQ) (TP := DCTX) (T := LLT) (sqb := map (Z_to_bv 8) sq);
      first [ eassumption | exact I ]. }
  intros ms' PO. unfold sq_inl_bitinit_L1_post in PO. cbv beta in PO.
  destruct PO as [(a2' & a4' & a5' & a7' & s11' & m' & cw & bc & jpad & -> & MU & WM & MI' & HBD & H32 & H56 & H64 & H104 & _ & BC & _ & BOK)
                 | (a0' & a1' & a2' & a3' & a4' & a5' & a7' & s11' & m' & bs & c32 & c56 & c64 & c104 & -> & MU & WM & MI' & HBD & H32 & H56 & H64 & H104)].
  - (* [comment removed for export] *)
    assert (MUL : munch [(FRB, FRB + 568); (FF, FF + 256)] m1 m') by i0_mul MU.
    i0_tr FR MU WM RGA8. i0_tr R40 MU WM RGA8. i0_tr R72 MU WM RGA8. i0_tr R112 MU WM RGA8. i0_tr FRF MU WM RGA8. i0_tr F72 MU WM RGA8.
    rewrite LN in HBD, BOK. unfold sbd_cells in HBD.
    i0_glue FR H32. i0_glue FR R40. i0_glue FR H56. i0_glue FR H64. i0_glue FR R72. i0_glue FR H104. i0_glue FR R112.
    i0_glue FRF HBD. i0_glue FRF F72.
    eapply (CONT m' (firstn 24 ja) (firstn 16 (skipn 8 (skipn 24 ja))) (firstn 8 jb) (firstn 8 (skipn 8 (skipn 8 jb))) jc jd je jf jg jh jseq jpad j72
              p0 p1 p2 cw bc (bitd_ptr SEQ (zlen sq)) x1 x5 x6 x7 a2' a4' a5' a7' s11' x28 x29 x30).
    + eapply TRANS; [exact MUL | exact WM | exact MI' | exact FR | exact FRF].
    + exact BC.
    + exact BOK.
  - (* [comment removed for export] *)
    assert (MUL : munch [(FRB, FRB + 568); (FF, FF + 256)] m1 m') by i0_mul MU.
    i0_tr FR MU WM RGA8. i0_tr R40 MU WM RGA8. i0_tr R72 MU WM RGA8. i0_tr R112 MU WM RGA8. i0_tr FRF MU WM RGA8. i0_tr F72 MU WM RGA8.
    i0_glue FR H32. i0_glue FR R40. i0_glue FR H56. i0_glue FR H64. i0_glue FR R72. i0_glue FR H104. i0_glue FR R112.
    i0_glue FRF HBD. i0_glue FRF F72.
    sql_blob_seg FR 23%nat 32%nat. sql_blob_seg FR 0%nat 22%nat. sql_blob_seg FRF 0%nat 7%nat.
    lazymatch type of FR with rw_cells _ _ _ [CB _ ?BA; _; CB _ ?BB] =>
    lazymatch type of FRF with rw_cells _ _ _ [CB _ ?BF; _] =>
      eapply (IERR m' BA BB BF x1 x5 x6 x7 a0' a1' a2' a3' a4' a5' p0 a7' (Z_to_bv 64 ASHOFF) (Z_to_bv 64 SEQ) (Z_to_bv 64 CAP) (Z_to_bv 64 (FF + 32))
                (Z_to_bv 64 DCTX) (Z_to_bv 64 nbSeq) (Z_to_bv 64 LBE) s11' x28 x29 x30 (Z_to_bv 64 (DCTX + 30368)))
    end end.
    eapply TRANS; [exact MUL | exact WM | exact MI' | exact FR | exact FRF].
Qed.

End CANSEC1.
