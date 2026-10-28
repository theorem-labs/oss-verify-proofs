(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_d_base RZ_seq_d_lbase RZ_seq_d_lkit RZ_seq_d_lbase2 huf411_kit_rs seqD_kit_rlc seqL2_kit_ck.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seqd_reload1 : forall P OEND LEND K, seqd_static P OEND LEND -> 1 <= K <= q_nbSeq P ->
  at_b898 P OEND LEND K -> at_b884 P OEND LEND K.
Proof.
  intros P OEND LEND K ST HK CONT. unfold at_b884.
  intros m1 cw bc ptr sLL sOF sML p0 p1 p2 LP OP nLL aLL bLL vLL nOF aOF bOF nML aML bML mlv ofs x1 x5 x6 x7 x12 x13 x14 x15 x17 x28 x29 x30 x31 INV LF NX HA1 HA2 HA3 HV HM.
  pose proof (seqd_linv_frame P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as TRANS.
  pose proof (seqd_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  pose proof INV as INVc.
  unfold at_b898 in CONT.
  destruct INV as ((j0 & jpad & jseq & FR) & _ & _ & _ & SQB & _).
  destruct LF as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_static seqd_frame seqd_post q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in *.
  pose proof ST as ST0. sd_static_open ST.
  remember (map (Z_to_bv 8) sq) as sqb eqn:Esqb. remember (zlen sq) as n eqn:En.
  assert (LSQ : Z.of_nat (length sqb) = n) by (subst sqb n; rewrite length_map; reflexivity).
  assert (MUL : munch [(SPV - 352, SPV)] m1 m1) by apply munch_refl. assert (WMl : wmono usegs m1 m1) by apply wmono_refl.
  assert (RS : 0 <= bc <= 9900000) by (clear - L6 HK S16; lia).
  assert (DJ : SPV - 352 + 352 <= SEQ \/ SEQ + n <= SPV - 352) by (unfold held in S25; clear - S25 S18; lia).
  assert (CASES : 65 <= bc \/ (bc <= 64 /\ ptr = SEQ) \/ (bc <= 64 /\ 8 <= n /\ SEQ + 8 <= ptr <= SEQ + n - 8) \/
                  (bc <= 64 /\ 8 <= n /\ SEQ + 1 <= ptr <= SEQ + 7 /\ ptr <= SEQ + n - 8)).
  { unfold bit_ok in L7. clear - L7. destruct (Z_le_gt_dec bc 64) as [B|B]; [|left; lia]. destruct (L7 B) as [E|(N8 & R)]; [right; left; lia|].
    destruct (Z_le_gt_dec (SEQ + 8) ptr); [right; right; left; lia|]. destruct (Z.eq_dec ptr SEQ); [right; left; lia| right; right; right; lia]. }
  clear L7.
  destruct CASES as [C|[C|[C|C]]].
  - (* [comment removed for export] *)
    try hold TRANS. try hold CONT. try hold HK. try hold L1. try hold L2. try hold L3. try hold L4. try hold L5. try hold L6. try hold En. try hold Esqb. try hold NX. try hold HV. try hold HM. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML. try hold ST0. try hold INVc.
    kx_autoLx [0x1cd70] 120%nat
    [KZRange SPV 544 (2^47); KZRange SEQ 4096 (2^47); KZRange n 1 (2^47); KZRange (SEQ + n) 4096 (2^47);
     KZRange aLL 0 16; KZRange aML 0 16; KZRange aOF 0 31; KZRange bc 65 9900000;
     KZWr (SPV - 352) 352; KZDisj (SPV - 352) 352 SEQ n]
    [(SEQ, n)].
    all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d724) _ _ _ _) => seql_ck end).
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]).
    all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in HK; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in En; try unfold held in Esqb; try unfold held in NX; try unfold held in HV; try unfold held in HM; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; try unfold held in ST0; try unfold held in INVc).
    all: (eapply CONT;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]
      | unfold seqd_lfacts, bit_ok; cbn [q_DST q_LITP q_tLL q_tOF q_tML q_SEQ q_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact NX | exact HA1 | exact HV | exact HM ]).

  - (* [comment removed for export] *)
    destruct C as (C1 & C2). subst ptr.
    try hold TRANS. try hold CONT. try hold HK. try hold L1. try hold L2. try hold L3. try hold L4. try hold L5. try hold L6. try hold En. try hold Esqb. try hold NX. try hold HV. try hold HM. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML. try hold ST0. try hold INVc.
    kx_autoLx [0x1cd70] 120%nat
    [KZRange SPV 544 (2^47); KZRange SEQ 4096 (2^47); KZRange n 1 (2^47); KZRange (SEQ + n) 4096 (2^47);
     KZRange aLL 0 16; KZRange aML 0 16; KZRange aOF 0 31; KZRange bc 0 64;
     KZWr (SPV - 352) 352; KZDisj (SPV - 352) 352 SEQ n]
    [(SEQ, n)].
    all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d724) _ _ _ _) => seql_ck end).
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]).
    all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in HK; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in En; try unfold held in Esqb; try unfold held in NX; try unfold held in HV; try unfold held in HM; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; try unfold held in ST0; try unfold held in INVc).
    all: (eapply CONT;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]
      | unfold seqd_lfacts, bit_ok; cbn [q_DST q_LITP q_tLL q_tOF q_tML q_SEQ q_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact NX | exact HA1 | exact HV | exact HM ]).

  - (* [comment removed for export] *)
    destruct C as (C1 & C2 & C3).
    assert (QR : exists q r d, bc = 8 * q + r /\ ptr = SEQ + d /\ 0 <= q <= 8 /\ 0 <= r <= 7 /\ 8 <= d /\ d + 8 <= n)
      by (exists (bc / 8), (bc mod 8), (ptr - SEQ); clear - C1 C3 RS; lia).
    destruct QR as (q & r & d & -> & -> & Q1 & Q2 & Q3 & Q4).
    try hold TRANS. try hold CONT. try hold HK. try hold L1. try hold L2. try hold L3. try hold L4. try hold L5. try hold L6. try hold En. try hold Esqb. try hold NX. try hold HV. try hold HM. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML. try hold ST0. try hold INVc.
    kx_autoLx [0x1cd70; 0x1df40] 120%nat
    [KZRange SPV 544 (2^47); KZRange SEQ 4096 (2^47); KZRange n 1 (2^47); KZRange (SEQ + n) 4096 (2^47);
     KZRange aLL 0 16; KZRange aML 0 16; KZRange aOF 0 31; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange d 8 (2^47); KZRange (d - q) 0 (2^47); KZRange (n - d) 8 (2^47); KZRange (n - d + q) 8 (2^47);
     KZWr (SPV - 352) 352; KZDisj (SPV - 352) 352 SEQ n]
    [(SEQ, n)].
    all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d724) _ _ _ _) => seql_ck end).
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]).
    all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in HK; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in En; try unfold held in Esqb; try unfold held in NX; try unfold held in HV; try unfold held in HM; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; try unfold held in ST0; try unfold held in INVc).
    all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1cd70) _ _ _ _) => (eapply CONT;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]
      | unfold seqd_lfacts, bit_ok; cbn [q_DST q_LITP q_tLL q_tOF q_tML q_SEQ q_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact NX | exact HA1 | exact HV | exact HM ])
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1df40) _ _ _ _) => idtac
      end.
    try rewrite En in ST0. try rewrite Esqb in ST0. try rewrite En in INVc. try rewrite Esqb in INVc.
    eapply evt_cut.
    { eapply (seqd_rl_spec (mkSDP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) OEND LEND m1 _ _ cw (8 * q + r) (SEQ + d) sLL sOF sML p0 p1 p2 LP jpad jseq);
        [ exact ST0 | exact INVc | exact MUL | exact WMl | exact KXMI | exact FR
        | first [reflexivity | (f_equal; cbn [q_SPV]; lia) | (cbn [q_SPV]; f_equal; lia)]
        | lia | cbn [q_SEQ]; lia | cbn [q_SEQ q_sq]; rewrite <- En; lia ]. }
    clear FR KXMI MUL WMl INVc. try clear SQB. try clear MI.
    intros ms2 (a1_ & a2_ & a3_ & a4_ & a5_ & a6_ & m2 & cw2 & -> & INV2 & FR).
    rewrite ret_pc_even by (first [reflexivity | lia]).
    cbn [q_SPV q_SEQ q_sq] in *.
    assert (EDIV : (8 * q + r) / 8 = q /\ (8 * q + r) mod 8 = r) by (clear - Q2; split; [symmetry; apply Z.div_unique with r; lia | symmetry; apply Z.mod_unique with q; lia]).
    try rewrite (proj1 EDIV) in INV2. try rewrite (proj2 EDIV) in INV2. try rewrite (proj1 EDIV) in FR. try rewrite (proj2 EDIV) in FR. clear EDIV.
    pose proof (seqd_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV2) as MI.
    cbn [tl seqd_frame seqd_post q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in FR.
    assert (MUL : munch [(SPV - 352, SPV)] m2 m2) by apply munch_refl. assert (WMl : wmono usegs m2 m2) by apply wmono_refl.
    try hold TRANS. try hold CONT. try hold HK. try hold L1. try hold L2. try hold L3. try hold L4. try hold L5. try hold L6. try hold En. try hold Esqb. try hold NX. try hold HV. try hold HM. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML. try hold ST0. try hold INV2.
    kx_autoLx [0x1cd70] 60%nat
    [KZRange SPV 544 (2^47); KZWr (SPV - 352) 352]
    [(SPV - 352, 352)].
    all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d724) _ _ _ _) => seql_ck end).
    all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in HK; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in En; try unfold held in Esqb; try unfold held in NX; try unfold held in HV; try unfold held in HM; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; try unfold held in ST0; try unfold held in INV2).
    all: (eapply CONT;
      [ first [exact INV2 | (eapply seqd_linv_frame; [exact ST0 | exact INV2 | exact MUL | exact WMl | first [exact KXMI | exact MI] | eapply seqd_frame_c8; exact FR])]
      | unfold seqd_lfacts, bit_ok; cbn [q_DST q_LITP q_tLL q_tOF q_tML q_SEQ q_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact NX | exact HA1 | exact HV | exact HM ]).

  - (* [comment removed for export] *)
    destruct C as (C1 & C2 & C3 & C4).
    assert (QR : exists q r d, bc = 8 * q + r /\ ptr = SEQ + d /\ 0 <= q <= 8 /\ 0 <= r <= 7 /\ 1 <= d <= 7 /\ d + 8 <= n)
      by (exists (bc / 8), (bc mod 8), (ptr - SEQ); clear - C1 C3 C4 RS; lia).
    destruct QR as (q & r & d & -> & -> & Q1 & Q2 & Q3 & Q4).
    destruct (Z_le_gt_dec q d) as [QD|QD].
    + try hold TRANS. try hold CONT. try hold HK. try hold L1. try hold L2. try hold L3. try hold L4. try hold L5. try hold L6. try hold En. try hold Esqb. try hold NX. try hold HV. try hold HM. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML. try hold ST0. try hold INVc.
      kx_autoLx [0x1cd70] 120%nat
    [KZRange SPV 544 (2^47); KZRange SEQ 4096 (2^47); KZRange n 1 (2^47); KZRange (SEQ + n) 4096 (2^47);
     KZRange aLL 0 16; KZRange aML 0 16; KZRange aOF 0 31; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange d 1 7; KZRange (d - q) 0 7; KZRange (n - d) 8 (2^47); KZRange (n - d + q) 8 (2^47);
     KZWr (SPV - 352) 352; KZDisj (SPV - 352) 352 SEQ n]
    [(SEQ, n)].
    all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d724) _ _ _ _) => seql_ck end).
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]).
    all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in HK; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in En; try unfold held in Esqb; try unfold held in NX; try unfold held in HV; try unfold held in HM; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; try unfold held in ST0; try unfold held in INVc).
    all: (eapply CONT;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]
      | unfold seqd_lfacts, bit_ok; cbn [q_DST q_LITP q_tLL q_tOF q_tML q_SEQ q_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact NX | exact HA1 | exact HV | exact HM ]).

    + try hold TRANS. try hold CONT. try hold HK. try hold L1. try hold L2. try hold L3. try hold L4. try hold L5. try hold L6. try hold En. try hold Esqb. try hold NX. try hold HV. try hold HM. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold OKLL. try hold OKOF. try hold OKML. try hold ST0. try hold INVc.
      kx_autoLx [0x1cd70] 120%nat
    [KZRange SPV 544 (2^47); KZRange SEQ 4096 (2^47); KZRange n 1 (2^47); KZRange (SEQ + n) 4096 (2^47);
     KZRange aLL 0 16; KZRange aML 0 16; KZRange aOF 0 31; KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange d 1 7; KZRange (q - d) 1 8; KZRange (n - d) 8 (2^47);
     KZWr (SPV - 352) 352; KZDisj (SPV - 352) 352 SEQ n]
    [(SEQ, n)].
    all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d724) _ _ _ _) => seql_ck end).
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]).
    all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in CONT; try unfold held in HK; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in En; try unfold held in Esqb; try unfold held in NX; try unfold held in HV; try unfold held in HM; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; try unfold held in ST0; try unfold held in INVc).
    all: (eapply CONT;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR]
      | unfold seqd_lfacts, bit_ok; cbn [q_DST q_LITP q_tLL q_tOF q_tML q_SEQ q_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact NX | exact HA1 | exact HV | exact HM ]).

Qed.
