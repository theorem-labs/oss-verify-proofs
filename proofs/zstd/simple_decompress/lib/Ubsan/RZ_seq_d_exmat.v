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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_d_base RZ_seq_d_lbase RZ_seq_d_lkit RZ_seq_d_lbase2 RZ_seq_d_lkit2 RZ_seq_d_lbase3 seqL2_kit_ck.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seqd_lfacts_lp : forall P OEND LEND B OP LP LP' bc ptr sLL sOF sML,
  seqd_lfacts P OEND LEND B OP LP bc ptr sLL sOF sML -> q_LITP P <= LP' <= LEND ->
  seqd_lfacts P OEND LEND B OP LP' bc ptr sLL sOF sML.
Proof. intros P OEND LEND B OP LP LP' bc ptr sLL sOF sML (L1 & L2 & L) H. split; [exact L1|]. split; [exact H| exact L]. Qed.

Lemma seqd_exec3 : forall P OEND LEND K, seqd_static P OEND LEND -> 1 <= K <= q_nbSeq P ->
  at_bfa4 P OEND LEND K -> at_bb64 P OEND LEND K -> at_bb28 P OEND LEND K -> at_bca4 P OEND LEND K -> at_bab4 P OEND LEND K.
Proof.
  intros P OEND LEND K ST HK CONT1 CONT2 CONT3 CONT4. unfold at_bab4.
  intros m1 cw bc ptr sLL sOF sML p0 p1 p2 LP OP llv mlv ofs ile sl ole x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x26 x28 x29 x30 x31 INV LF HO FAST E1 E2 E3.
  pose proof (seqd_linv_frame P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as TRANS.
  pose proof (seqd_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  unfold at_bfa4 in CONT1. unfold at_bb64 in CONT2. unfold at_bb28 in CONT3. unfold at_bca4 in CONT4.
  pose proof INV as ((j0 & jpad & jseq & FR) & _).
  pose proof LF as LF0. destruct LF as (L1 & L2 & _). pose proof FAST as FAST0. destruct FAST as (F1 & F2 & F3 & F4).
  pose proof ST as ST0.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_static seqd_frame seqd_post q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in ST, FR, L1, L2, CONT1, CONT2, CONT3, CONT4, TRANS |- *.
  sd_static_open ST. pose proof ALSP as [AL4].
  assert (MUL : munch [(SPV - 352, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  assert (RG : 4096 <= ole < 2^47 /\ 4096 <= PFX < 2^47 /\ 4096 <= ile < 2^47 /\ 0 <= mlv <= 262143 /\ 0 <= sl < 2^19)
    by (clear - L1 L2 S1 S2 S3 S4 S5 S6 S7 S9 S11 F1 F2 F3 F4 E1 E2 E3; lia).
  destruct (Z_le_gt_dec ofs (ole - PFX)) as [CA|CB].
  - (* [comment removed for export] *)
    assert (RA : 0 <= ole - PFX - ofs <= 2^47 /\ 4096 <= ole - ofs <= 2^47 /\ 0 <= ofs <= 2^47) by (clear - CA HO RG; lia).
    (try hold CONT1; try hold CONT2; try hold CONT3; try hold CONT4; try hold TRANS; try hold HK; try hold LF0; try hold ST0; try hold FAST0; try hold INV; try hold L2; try hold F3; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML).
    kx_autoLx [0x1d2c0; 0x35670; 0x1d124; 0x1d0c8; 0x1d6e4; 0x1d724] 60%nat
    [KZRange SPV 544 (2^47); KZAlign SPV 16; KZRange ole 4096 (2^47); KZRange PFX 4096 (2^47); KZRange ile 4096 (2^47); KZRange mlv 0 262143;
     KZRange ofs 0 (2^47); KZRange (ole - PFX) 0 (2^47); KZRange (ole - PFX - ofs) 0 (2^47); KZRange (ole - ofs) 4096 (2^47); KZRange sl 0 (2^19); KZWr (SPV - 352) 352]
    [(SPV - 352, 352)].
    all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d724) _ _ _ _) => seql_ck end).
    all: kx_mem.
    all: (try unfold held in CONT1; try unfold held in CONT2; try unfold held in CONT3; try unfold held in CONT4; try unfold held in TRANS; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in FAST0; try unfold held in INV; try unfold held in L2; try unfold held in F3; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d2c0) _ _ _ _) =>
          eapply CONT4; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | eapply seqd_lfacts_lp; [exact LF0 | cbn [q_LITP]; lia] | unfold seqd_mfast; cbn [q_DST]; lia | lia | cbn [q_PFX]; lia | lia | lia | cbn [q_PFX]; lia ]
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x35670) _ _ _ _) =>
          eapply evt_cut; [eapply seqd_copy_spec; [exact ST0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | cbn [q_DST]; lia | lia | lia | right; cbn [q_B0 q_B1]; lia]|]; sd_copy_intro INV2
      end.
    all: clear TRANS FR MUL WMl. all: try clear MI. all: try clear KXMI. all: try clear j0 jpad jseq.
    all: pose proof (seqd_linv_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST0 INV2) as TRANS.
    all: pose proof (seqd_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV2) as MI.
    all: pose proof INV2 as INV0; destruct INV2 as ((j0 & jpad & jseq & FR) & _).
    all: cbn [seqd_frame seqd_post q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in TRANS, FR.
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (MUL : munch [(SPV - 352, SPV)] mm mm) by apply munch_refl; assert (WMl : wmono usegs mm mm) by apply wmono_refl end.
    all: (try hold CONT1; try hold CONT2; try hold CONT3; try hold CONT4; try hold TRANS; try hold INV0; try hold INV; try hold HK; try hold LF0; try hold ST0; try hold FAST0; try hold L2; try hold F3; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML).
    all: kx_autoLx [0x1d124; 0x1d0c8; 0x1d2c0; 0x35670; 0x1d6e4; 0x1d724] 60%nat
    [KZRange SPV 544 (2^47); KZAlign SPV 16; KZRange ole 4096 (2^47); KZRange mlv 0 262143; KZRange ofs 16 (2^47); KZRange (ole - ofs) 4096 (2^47); KZRange sl 0 (2^19); KZWr (SPV - 352) 352]
    [(SPV - 352, 352)].
    all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d724) _ _ _ _) => seql_ck end).
    all: kx_mem.
    all: (try unfold held in CONT1; try unfold held in CONT2; try unfold held in CONT3; try unfold held in CONT4; try unfold held in TRANS; try unfold held in INV0; try unfold held in INV; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in FAST0; try unfold held in L2; try unfold held in F3; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d124) _ _ _ _) =>
          eapply CONT2; [first [exact INV0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]] | lia | right; split; [eapply seqd_lfacts_lp; [exact LF0 | cbn [q_LITP]; lia] | lia]]
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d0c8) _ _ _ _) =>
          eapply CONT3 with (ole := ole) (mlv := mlv) (ofs := ofs); [first [exact INV0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]] | eapply seqd_lfacts_lp; [exact LF0 | cbn [q_LITP]; lia] | unfold seqd_mfast; cbn [q_DST]; lia | cbn [q_PFX]; lia | lia | lia | lia]
      | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => exfalso; lia
      end.
  - (* [comment removed for export] *)
    assert (RB : 1 <= ofs - ole + PFX <= 18446744073709551615 /\ 1 <= ofs <= 18446744073709551615 /\ 0 <= ole - PFX <= 2^47) by (clear - CB HO RG S3 L1 E3 F1; lia).
    (try hold CONT1; try hold CONT2; try hold CONT3; try hold CONT4; try hold TRANS; try hold HK; try hold LF0; try hold ST0; try hold FAST0; try hold INV; try hold L2; try hold F3; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML).
    kx_autoLx [0x1d6e4; 0x1d2c0; 0x35670; 0x1d124; 0x1d0c8; 0x1d724] 60%nat
    [KZRange SPV 544 (2^47); KZAlign SPV 16; KZRange ole 4096 (2^47); KZRange PFX 4096 (2^47); KZRange ile 4096 (2^47); KZRange mlv 0 262143;
     KZRange ofs 1 18446744073709551615; KZRange (ole - PFX) 0 (2^47); KZRange (ofs - ole + PFX) 1 18446744073709551615; KZRange sl 0 (2^19); KZWr (SPV - 352) 352]
    [(SPV - 352, 352)].
    all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d724) _ _ _ _) => seql_ck end).
    all: kx_mem.
    all: (try unfold held in CONT1; try unfold held in CONT2; try unfold held in CONT3; try unfold held in CONT4; try unfold held in TRANS; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in FAST0; try unfold held in INV; try unfold held in L2; try unfold held in F3; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d6e4) _ _ _ _) => eapply CONT1 with (OP := 0); [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR] | lia | left; reflexivity]
      | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => exfalso; lia
      end.
Qed.

Lemma seqd_matloop_aux : forall (k : nat) P OEND LEND K, seqd_static P OEND LEND -> 1 <= K <= q_nbSeq P ->
  at_bb64 P OEND LEND K ->
  forall (m1 : fmem) (cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (ole mlv sl ofs cur src ome : Z) (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x23 x26 x28 x29 x30 x31 : word),
  seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP -> seqd_lfacts P OEND LEND (100 + 100 * (q_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  seqd_mfast P OEND OP ole mlv sl -> 16 <= ofs <= ole - q_PFX P -> ome = ole + mlv -> ole + 16 <= cur < ome -> src = cur - ofs + 16 ->
  ome - cur <= 32 * (Z.of_nat k + 1) ->
  evt usegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -352)) (q_gp P) (q_tp P) x5 x6 x7 x8 (Z_to_bv 64 src) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 K) (Z_to_bv 64 18446744073709551599) x20 x21 (Z_to_bv 64 ome) x23 (Z_to_bv 64 OP) (Z_to_bv 64 sl) x26 (Z_to_bv 64 cur) x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1d0c8) (q_fc P) None m1 (seg_rom usegs)).
Proof.
  induction k as [|k IHk]; intros P OEND LEND K ST HK CONT1 m1 cw bc ptr sLL sOF sML p0 p1 p2 LP OP ole mlv sl ofs cur src ome x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x23 x26 x28 x29 x30 x31 INV LF MF HOF EM HC ES HM.
  all: pose proof CONT1 as CONT0; unfold at_bb64 in CONT1.
  all: pose proof LF as LF0; destruct LF as (L1 & L2 & _); pose proof MF as MF0; destruct MF as (M1 & M2 & M3 & M4).
  all: pose proof ST as ST0.
  all: destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  all: cbn [seqd_static seqd_post q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in ST, L1, L2, M1, HOF, CONT1 |- *.
  all: sd_static_open ST.
  all: pose proof ALSP as [AL4].
  all: assert (RG : 4096 <= cur < 2^47 /\ 4096 <= src < 2^47 /\ 4096 <= ome < 2^47 /\ 0 <= sl < 2^47) by (clear - L1 S1 S2 S3 S4 S5 S6 S7 M1 M2 M3 M4 HOF EM HC ES; lia).
  all: (try hold CONT1; try hold CONT0; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold HM; try hold HOF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML).
  all: kx_autoLx [0x35670; 0x1d0c8; 0x1d124; 0x1d724] 40%nat
    [KZRange SPV 544 (2^47); KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange ome 4096 (2^47)]
    [].
  all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d724) _ _ _ _) => seql_ck end).
  all: kx_mem.
  all: (try unfold held in CONT1; try unfold held in CONT0; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in HM; try unfold held in HOF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
  all: lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x35670) _ _ _ _) =>
        eapply evt_cut; [eapply seqd_copy_spec; [exact ST0 | exact INV | cbn [q_DST]; lia | lia | lia | right; cbn [q_B0 q_B1]; lia]|]; sd_copy_intro INV1
    end.
  all: (try hold CONT1; try hold CONT0; try hold IHk; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold HM; try hold HOF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML).
  all: kx_autoLx [0x35670; 0x1d0c8; 0x1d124; 0x1d724] 40%nat
    [KZRange SPV 544 (2^47); KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange ome 4096 (2^47)]
    [].
  all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d724) _ _ _ _) => seql_ck end).
  all: kx_mem.
  all: (try unfold held in CONT1; try unfold held in CONT0; try unfold held in IHk; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in HM; try unfold held in HOF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
  all: lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x35670) _ _ _ _) =>
        eapply evt_cut; [eapply seqd_copy_spec; [exact ST0 | exact INV1 | cbn [q_DST]; lia | lia | lia | right; cbn [q_B0 q_B1]; lia]|]; sd_copy_intro INV2
    end.
  all: pose proof (seqd_linv_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST0 INV2) as TRANS.
  all: pose proof (seqd_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV2) as MI.
  all: pose proof INV2 as INV0; destruct INV2 as ((j0 & jpad & jseq & FR) & _).
  all: cbn [seqd_frame seqd_post q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in TRANS, FR.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (MUL : munch [(SPV - 352, SPV)] mm mm) by apply munch_refl; assert (WMl : wmono usegs mm mm) by apply wmono_refl end.
  all: (try hold CONT1; try hold CONT0; try hold IHk; try hold TRANS; try hold INV0; try hold HK; try hold LF0; try hold ST0; try hold MF0; try hold HM; try hold HOF; try hold S1; try hold S2; try hold S3; try hold S4; try hold S5; try hold S6; try hold S7; try hold S8; try hold S9; try hold S10; try hold S11; try hold S12; try hold S13; try hold S14; try hold S15; try hold S16; try hold S18; try hold S19; try hold S20; try hold S21; try hold S22; try hold S23; try hold S24; try hold S25; try hold S26; try hold S27; try hold S28; try hold S29; try hold S30; try hold S31; try hold S32; try hold S33; try hold S34; try hold S35; try hold OKLL; try hold OKOF; try hold OKML).
  all: kx_autoLx [0x1d0c8; 0x1d124; 0x35670; 0x1d724] 40%nat
    [KZRange SPV 544 (2^47); KZAlign SPV 16; KZRange cur 4096 (2^47); KZRange src 4096 (2^47); KZRange ome 4096 (2^47); KZRange sl 0 (2^47); KZWr (SPV - 352) 352]
    [(SPV - 352, 352)].
  all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d724) _ _ _ _) => seql_ck end).
  all: kx_mem.
  all: (try unfold held in CONT1; try unfold held in CONT0; try unfold held in IHk; try unfold held in TRANS; try unfold held in INV0; try unfold held in HK; try unfold held in LF0; try unfold held in ST0; try unfold held in MF0; try unfold held in HM; try unfold held in HOF; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end).
  all: lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d0c8) _ _ _ _) =>
        first [exfalso; lia | eapply (IHk _ OEND LEND K ST0 HK CONT0) with (ole := ole) (mlv := mlv) (ofs := ofs); [first [exact INV0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]] | exact LF0 | exact MF0 | cbn [q_PFX]; lia | lia | lia | lia | lia]]
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d124) _ _ _ _) =>
        eapply CONT1; [first [exact INV0 | eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]] | lia | right; split; [exact LF0 | lia]]
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => exfalso; lia
    end.
Qed.

Lemma seqd_matloop : forall P OEND LEND K, seqd_static P OEND LEND -> 1 <= K <= q_nbSeq P ->
  at_bb64 P OEND LEND K -> at_bb28 P OEND LEND K.
Proof.
  intros P OEND LEND K ST HK CONT1. unfold at_bb28.
  intros m1 cw bc ptr sLL sOF sML p0 p1 p2 LP OP ole mlv sl ofs cur src ome x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x23 x26 x28 x29 x30 x31 INV LF MF HOF EM HC ES.
  eapply (seqd_matloop_aux (Z.to_nat (ome - cur)) P OEND LEND K ST HK CONT1); try eassumption. lia.
Qed.
