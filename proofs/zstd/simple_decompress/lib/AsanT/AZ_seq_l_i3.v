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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_hkit AZ_seq_l_ibase AZ_seq_l_iat AZ_seq_l_ikit AZ_seq_inl_initfse_L2.
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

Section CANSEC1. Context {rc : runConstT}.

Ltac lg3_hat H A := lazymatch type of H with rw_cells ?sg ?mm ?B ?cs => replace B with A in H by (cbn [cells_size csize Nat.add length app sbd_cells]; clear; lia) end.
Ltac lg3_at A := lazymatch goal with |- rw_cells ?sg ?mm ?B ?cs => replace B with A by (cbn [cells_size csize Nat.add length app sbd_cells]; clear; lia) end.

Lemma lg3_c8_cb8 : forall (m1 : amem) A (w : word) post,
  rw_cells bsegs m1 A (C8 w :: post) -> rw_cells bsegs m1 A (CB 8 (le8 w) :: post).
Proof.
  intros m1 A w post H. pose proof H as [[WF _] _]. destruct WF as [_ WF2].
  eapply rw_cells_recell; [exact H | cbn [cells_wf cell_wf]; split; [apply length_le8 | exact WF2] | reflexivity].
Qed.

Lemma sql_i3_ok : forall P OEND, sql_static P OEND (l_LITP P) (l_LBE P) (l_LOC P) ->
  (l_LLT P + 4104 < 2^47 /\ l_OFT P + 2056 < 2^47 /\ l_MLT P + 4104 < 2^47) ->
  ai_I5 P OEND -> ai_I3 P OEND.
Proof.
  intros P OEND ST TST CONT.
  unfold ai_I3. intros m1 ja jb jc jd je jf jg jh jk ji jr jseq jpad j88 p0 p1 p2 cw bc ptr sLL x1 x5 x12 x14 x15 x17 x27 x28 x29 x30 INV HBC BOK HS1.
  unfold ai_I5 in CONT.
  pose proof (sql_iasan_now _ _ _ _ _ _ _ _ ST INV) as ASN.
  pose proof (sql_itbl_asan _ _ _ _ _ _ _ _ ST INV) as (ATL & ATO & ATM).
  pose proof (sql_iinv_mi _ _ _ _ _ _ _ _ INV) as MI.
  pose proof INV as (_ & _ & _ & _ & TOFb & _).
  apply (sql_iopen_k _ _ _ _ _ _ _ _ ST INV); intros FR0 FF0 PT SQB _ UFL USQ RSQ RSQS UD RD RDS.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  cbv delta [sql_iregsB sql_ifrB sql_iffC sql_iffD sql_asan] in *.
  cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in *.
  pose proof ST as STc. sd_static_open STc. unfold held in *.
  destruct S61 as (ASTK & _ & _ & _ & ED8 & _ & _ & _ & _ & _ & ESHF & RFF & RSHF & _).
  destruct ASN as (_ & _ & _ & _ & ACL & _ & _ & _ & _ & ART).
  pose proof (proj1 OKOF) as TRO. cbn [kind_maxLog] in TRO.
  pose proof (proj1 OKML) as TRM. cbn [kind_maxLog] in TRM.
  assert (PO8 : 1 <= 2 ^ st_log tOF <= 256).
  { clear - TRO. split; [pose proof (Z.pow_pos_nonneg 2 (st_log tOF)); lia | change 256 with (2^8); apply Z.pow_le_mono_r; lia]. }
  assert (PM0 : 0 <= 2 ^ st_log tML) by (clear - TRM; apply Z.pow_nonneg; lia).
  assert (LN : Z.of_nat (length (map (Z_to_bv 8) sq)) = zlen sq) by (rewrite length_map; reflexivity).
  (* [comment removed for export] *)
  rewrite !app_assoc in FR0.
  apply rw_cells_app in FR0 as (FRa & FR4). apply rw_cells_app in FRa as (FRp & FR272).
  cbn [app] in FRp. lg3_hat FR272 (FRB + 272). lg3_hat FR4 (FRB + 304).
  destruct (sql_cb16_words m1 (FRB + 272) [] jh [C8 (Z_to_bv 64 (LLT + 8)); CB 8 jk] FR272) as (h1 & h2 & FR272b).
  change (rw_cells bsegs m1 (FRB + 272) ([C8 h1] ++ ([C8 h2] ++ [C8 (Z_to_bv 64 (LLT + 8)); CB 8 jk]))) in FR272b.
  apply rw_cells_app in FR272b as (FH1 & FR272c). apply rw_cells_app in FR272c as (FH2 & FL).
  lg3_hat FH2 (FRB + 280). lg3_hat FL (FRB + 288).
  destruct (sql_cbst32 m1 FF [CB 32 jfh; C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 SEQ); C8 (Z_to_bv 64 (SEQ + 8)); C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (LLT + 8))] j88 [C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))] FF0) as (w1 & w2 & j' & FF1).
  change (rw_cells bsegs m1 FF ([CB 32 jfh] ++ ([C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 SEQ); C8 (Z_to_bv 64 (SEQ + 8))] ++
    ([C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (LLT + 8))] ++ ([C8 w1; C8 w2] ++ (CB 16 j' :: [C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))])))))) in FF1.
  apply rw_cells_app in FF1 as (FA & FF2). apply rw_cells_app in FF2 as (FB & FF3).
  apply rw_cells_app in FF3 as (FC & FF4). apply rw_cells_app in FF4 as (FD & FE).
  lg3_hat FB (FF + 32). lg3_hat FC (FF + 32 + 40). lg3_hat FD (FF + 32 + 56). lg3_hat FE (FF + 32 + 72).
  unfold dctx_ptrs in PT.
  change (rw_cells bsegs m1 DCTX ([C8 (Z_to_bv 64 LLT)] ++ ([C8 (Z_to_bv 64 MLT)] ++ [C8 (Z_to_bv 64 OFT); C8 huf]))) in PT.
  apply rw_cells_app in PT as (_ & PT2). apply rw_cells_app in PT2 as (PM & _).
  change (rw_cells bsegs m1 (DCTX + 8) [C8 (Z_to_bv 64 MLT)]) in PM.
  assert (M1 : (FF + 32) mod 8 = 0) by (clear - S51; Z.div_mod_to_equations; lia).
  assert (M2 : OFT mod 4 = 0) by (clear - S45; Z.div_mod_to_equations; lia).
  assert (M3 : FRB mod 8 = 0) by (clear - S48; Z.div_mod_to_equations; lia).
  assert (M4 : DCTX mod 8 = 0) by (clear - ED8; Z.div_mod_to_equations; lia).
  assert (M5 : MLT mod 4 = 0) by (clear - S46; Z.div_mod_to_equations; lia).
  assert (APB : app_blk (FF + 32) (FF + 32 + 40)) by (unfold app_blk, KLOW, KHIGH, KEND; clear - S49 S50 S18 S17; lia).
  assert (APS : app_blk (FF + 32 + 56) (FF + 32 + 72)) by (unfold app_blk, KLOW, KHIGH, KEND; clear - S49 S50 S18 S17; lia).
  assert (APF : app_blk (FRB + 280) (FRB + 288)) by (destruct ASTK as (KHL & _ & _); unfold app_blk, KEND; clear - KHL S18 S47 S17; lia).
  assert (RGF : rng RNG (FRB + 280) 8) by (destruct ASTK as (_ & RST & _); eapply rng_sub'; [exact RST | clear - S18 S47 S17; lia]).
  assert (AOW : aro RNG m1 (FF + 32) 112).
  { split; [exact UFL|].
    split; [eapply rng_sub; [exact RFF | clear; lia | clear; lia]|].
    eapply rng_sub; [exact RSHF | |]; rewrite ESHF; unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - S51; Z.div_mod_to_equations; lia. }
  assert (AOB : aro RNG m1 (FF + 32) 40) by (eapply aro_sub; [exact AOW | clear; lia | clear; lia | clear; lia]).
  assert (AOS : aro RNG m1 (FF + 32 + 56) 16) by (eapply aro_sub; [exact AOW | clear; lia | clear; lia | clear; lia]).
  assert (AOD : aro RNG m1 (DCTX + 8) 8)
    by (eapply aro_sub; [split; [exact UD | split; [exact RD | exact RDS]] | clear; lia | clear; lia | clear; unfold DCTX_SIZEOF; lia]).
  assert (AOM : aro RNG m1 MLT 8) by (eapply aro_sub; [exact ATM | clear; lia | clear; lia | clear - PM0; lia]).
  assert (AOQ : aro RNG m1 SEQ (Z.of_nat (length (map (Z_to_bv 8) sq)))) by (rewrite LN; split; [exact USQ | split; [exact RSQ | exact RSQS]]).
  assert (IB : bit_okS SEQ (Z.of_nat (length (map (Z_to_bv 8) sq))) bc ptr) by (unfold bit_okS; rewrite LN; exact BOK).
  pose proof sq_inl_initfse_L2_proof as W. unfold sq_inl_initfse_L2_stmt, sq_inl_initfse_L2_stmt_if in W. cbv beta in W.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply W with (m := m1) (FRB := FRB) (BD := FF + 32) (T := OFT) (SEQ := SEQ) (B := 73) (bc := bc) (ptr := ptr) (TP := DCTX) (MT := MLT)
                  (STL := sLL) (cw := cw) (st0 := w1) (tb0 := w2) (c280 := h2) (jpad := jpad) (sqb := map (Z_to_bv 8) sq) (k := K_OF) (t := tOF).
    all: try exact I.
    all: try eassumption.
    all: try rewrite LN.
    all: try (clear - S13 S14 S15 S17 S18 S19 S20 S22 S23 S47 S50 TST PO8; lia).
    all: try (clear - S49; lia).
    all: try (clear - S56; lia).
    all: try (clear - S59 PO8; lia).
    all: try (clear - S25 S18 S47; lia).
    all: try (clear - S29 S18 S47 PO8; lia).
    all: try (clear - S54; lia).
    all: clear - S27 S18 S47; lia. }
  intros ms' PO. unfold sq_inl_initfse_L2_post in PO.
  destruct PO as (t0' & t3' & t5' & a0' & a1' & a2' & a3' & a4' & a5' & a7' & m' & cw' & bc' & jpad' & ptr' & st' & -> & MU & WM & MI' & HBD' & HST' & H280' & E0 & E3 & E5 & EA0 & EA1 & STB & BCB & BOK').
  subst t0' t3' t5' a0' a1'.
  pose proof (rw_cells_transport bsegs _ _ _ _ _ FA MU WM) as FA'.
  specialize (FA' ltac:(cbn [disjoint_from cells_size csize Nat.add length]; repeat split; clear - S47 S18 S50; lia)).
  pose proof (rw_cells_transport bsegs _ _ _ _ _ FC MU WM) as FC'.
  specialize (FC' ltac:(cbn [disjoint_from cells_size csize Nat.add length]; repeat split; clear - S47 S18 S50; lia)).
  pose proof (rw_cells_transport bsegs _ _ _ _ _ FE MU WM) as FE'.
  specialize (FE' ltac:(cbn [disjoint_from cells_size csize Nat.add length]; repeat split; clear - S47 S18 S50; lia)).
  pose proof (rw_cells_transport bsegs _ _ _ _ _ FRp MU WM) as FRp'.
  specialize (FRp' ltac:(cbn [disjoint_from cells_size csize Nat.add length]; repeat split; clear - S47 S18 S50; lia)).
  pose proof (rw_cells_transport bsegs _ _ _ _ _ FH1 MU WM) as FH1'.
  specialize (FH1' ltac:(cbn [disjoint_from cells_size csize Nat.add length]; repeat split; clear - S47 S18 S50; lia)).
  pose proof (rw_cells_transport bsegs _ _ _ _ _ FL MU WM) as FL'.
  specialize (FL' ltac:(cbn [disjoint_from cells_size csize Nat.add length]; repeat split; clear - S47 S18 S50; lia)).
  pose proof (rw_cells_transport bsegs _ _ _ _ _ FR4 MU WM) as FR4'.
  specialize (FR4' ltac:(cbn [disjoint_from cells_size csize Nat.add length]; repeat split; clear - S47 S18 S50; lia)).
  pose proof (lg3_c8_cb8 m' (FRB + 272) h1 [] FH1') as FH1b.
  assert (MUL : munch [(FRB, FRB + 568); (FF, FF + 256)] m1 m').
  { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]. intros z Hz. clear - Hz. lia. }
  apply (CONT m' ja jb jc jd je jf jg (le8 h1) jk ji jr jseq jpad' j' p0 p1 p2 cw' bc' ptr' sLL st' x1 (Z_to_bv 64 sLL) a2' a3' a4' a5' a7' x27 x29).
  - eapply (sql_iinv_frame _ _ _ _ _ _ _ _ ST INV m' _ _ MUL WM MI').
    + cbn [l_FRB]. rewrite !app_assoc.
      apply rw_cells_app; split; [|lg3_at (FRB + 304); exact FR4'].
      apply rw_cells_app; split; [exact FRp'|].
      lg3_at (FRB + 272).
      lazymatch goal with |- rw_cells ?sg ?mm ?A [?a; ?b; ?c; ?d] => change (rw_cells sg mm A ([a] ++ ([b] ++ [c; d]))) end.
      apply rw_cells_app; split; [exact FH1b|].
      apply rw_cells_app; split; [lg3_at (FRB + 280); exact H280' | lg3_at (FRB + 288); exact FL'].
    + cbn [l_FF].
      change (rw_cells bsegs m' FF ([CB 32 jfh] ++ (sbd_cells cw' bc' jpad' ptr' SEQ ++ ([C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (LLT + 8))] ++
        ([C8 (Z_to_bv 64 st'); C8 (Z_to_bv 64 (OFT + 8))] ++ (CB 16 j' :: [C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))])))))).
      apply rw_cells_app; split; [exact FA'|].
      apply rw_cells_app; split; [lg3_at (FF + 32); exact HBD'|].
      apply rw_cells_app; split; [lg3_at (FF + 32 + 40); exact FC'|].
      apply rw_cells_app; split; [lg3_at (FF + 32 + 56); exact HST' | lg3_at (FF + 32 + 72); exact FE'].
  - clear - BCB; lia.
  - unfold bit_ok. unfold bit_okS in BOK'. rewrite LN in BOK'. exact BOK'.
  - exact HS1.
  - exact STB.
Qed.

End CANSEC1.
