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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_v_la AZ_seq_l_hkit AZ_seq_l_la_at AZ_seq_l_lkit2 AZ_seq_l_rlkit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
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

Lemma la_reload1 : forall P OEND LLO LEND LOCV K, sql_static P OEND LLO LEND LOCV -> 1 <= K <= l_nbSeq P ->
  la_rl1 P OEND LLO LEND LOCV K -> la_dec P OEND LLO LEND LOCV K.
Proof.
  (* [comment removed for export] *)
  intros P OEND LLO LEND LOCV K ST HK  CONT.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  unfold la_dec. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1].
  intros m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c232 c248 c264 c320 c352 c376 cw bc ptr sLL sOF sML p1 p2 rl rm ro LP OP nLL aLL bLL vLL nOF aOF bOF nML aML bML mlv ofs cnt sn raddr rem8 x11 x12 x20 INV LF NX HA1 HA2 HA3 HV HM HCNT HSN HSR HRA HRE HRING HOPD.
  unfold la_rl1 in CONT. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in HK, CONT.
  pose proof (sql_linv_frame _ _ _ _ _ m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 (Z_to_bv 64 (nbSeq - 1)) c232 c248 c264 (Z_to_bv 64 LEND) (Z_to_bv 64 (MLT + 8)) c320 (Z_to_bv 64 (LLT + 8)) (Z_to_bv 64 139648) c352 (Z_to_bv 64 (OFT + 8)) c376 cw bc ptr sLL sOF sML ofs p1 p2 rl rm ro LP ST INV) as TRANS. cbn [sql_frame sql_ffr l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in TRANS.
  
  apply (sql_lopen_k _ _ _ _ _ m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 (Z_to_bv 64 (nbSeq - 1)) c232 c248 c264 (Z_to_bv 64 LEND) (Z_to_bv 64 (MLT + 8)) c320 (Z_to_bv 64 (LLT + 8)) (Z_to_bv 64 139648) c352 (Z_to_bv 64 (OFT + 8)) c376 cw bc ptr sLL sOF sML ofs p1 p2 rl rm ro LP ST INV); cbn [sql_ffr l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros jpad jseq FR FRF L16F LJF SQB MI UFL USEQ RSQ RSQS.
  apply sql_fr_vla in FR. cbv delta [sql_ffr] in FRF. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in FR, FRF.
  apply (sql_lf_k _ _ _ _ _ _ _ _ _ _ _ _ LF); cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros L1 L2 L3 L4 L5 L6 L7.
  apply (sql_rg_k _ _ _ _ _ ST); cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  pose proof ST as ST0. sd_static_open ST. unfold held in RGB.
  remember (map (Z_to_bv 8) sq) as sqb eqn:Esqb. remember (zlen sq) as n eqn:En. try rewrite <- En in USEQ. try rewrite <- En in RSQ. try rewrite <- En in RSQS.
  assert (DJF : FF + 256 <= SEQ \/ SEQ + n <= FF) by (unfold held in S56; clear - S56 En; lia). assert (DJR : FRB + 568 <= SEQ \/ SEQ + n <= FRB) by (unfold held in S25; clear - S25 S18 S47 En; lia).
  assert (LSQ : Z.of_nat (length sqb) = n) by (subst sqb n; rewrite length_map; reflexivity).
  assert (MUL : munch [(FRB, FRB + 568); (FF, FF + 256)] m1 m1) by apply munch_refl. assert (WMl : wmono bsegs m1 m1) by apply wmono_refl.
  assert (RS : 0 <= bc <= 9900000) by (clear - L6 HK S16; lia).
  assert (DJ : SPV - 568 + 568 <= SEQ \/ SEQ + n <= SPV - 568) by (unfold held in S25; clear - S25 S18; lia). clear DJ.
  
  assert (CASES : 65 <= bc \/ (bc <= 64 /\ ptr = SEQ) \/ (bc <= 64 /\ 8 <= n /\ SEQ + 8 <= ptr <= SEQ + n - 8) \/
                  (bc <= 64 /\ 8 <= n /\ SEQ + 1 <= ptr <= SEQ + 7 /\ ptr <= SEQ + n - 8)).
  { unfold bit_ok in L7. clear - L7. destruct (Z_le_gt_dec bc 64) as [B|B]; [|left; lia]. destruct (L7 B) as [E|(N8 & R)]; [right; left; lia|].
    destruct (Z_le_gt_dec (SEQ + 8) ptr); [right; right; left; lia|]. destruct (Z.eq_dec ptr SEQ); [right; left; lia| right; right; right; lia]. }
  clear L7.
  destruct CASES as [C|[C|[C|C]]].
  - (* [comment removed for export] *)
    try hold TRANS. try hold ST0. try hold CONT. try hold HK. try hold L1. try hold L2. try hold L3. try hold L4. try hold L5. try hold L6. try hold En. try hold Esqb. try hold NX. try hold HV. try hold HM. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold S43. try hold S44. try hold S45. try hold S46. try hold S47. try hold S48. try hold S49. try hold S50. try hold S51. try hold S52. try hold S53. try hold S54. try hold S55. try hold S56. try hold S57. try hold S58. try hold S59. try hold S60. try hold S61. try hold S62. try hold S63. try hold S64. try hold S65. try hold S66. try hold S67. try hold S68. try hold S69. try hold S70. try hold S71. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoFLA (FR, FRF) [KAApp FRB 568; KAApp FF 256; KAUnp SEQ n] [0x8a860; 0x8ad30; 0x8ad3c; 0x8ad48] 480%nat
    [KZRange SPV 5056 (2^47); KZRange FRB 4096 (2^47); KZRange FF 6443008 (2^47); KZAlign SPV 16; KZAlign FF 8; KZRange (SEQ + n) 4097 (2^47 - 1);
     KZRange aLL 0 16; KZRange aML 0 16; KZRange aOF 0 31; KZRange SEQ 4096 (2^47 - 2); KZRange n 1 (2^47); KZRange bc 65 9900000;
     KZWr FRB 568; KZWr FF 256; KZDisj FF 256 FRB 568; KZDisj FRB 568 SEQ n; KZDisj FF 256 SEQ n]
    [(SEQ, n); (FRB, 568); (FF, 256)]
    [(FRB, 568); (FF, 256); (SEQ, n)].
    all: try clear DJ DJF DJR.
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]).
    all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
    all: try (lazymatch goal with |- sc_resid _ _ _ (SCDisj _ _ _ _) => kx_side_pre; try sql_oranges; try sql_bvr; try revert C'; try revert RGB; try revert RGA1; try revert RGA2; try revert RGA8; try revert RGC1; try revert RGC2; sql_clear_nonkx; intros; lia end).
    all: try sql_aclose.
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in ST0; try unfold held in CONT; try unfold held in HK; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in En; try unfold held in Esqb; try unfold held in NX; try unfold held in HV; try unfold held in HM; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
    all: lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8a860) _ _ _ _) => (eapply (CONT _ _ _ _ _ _ _ _ (Z_to_bv 64 0) _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) (Z_to_bv 64 0));
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact (sql_fr_ula _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ _ _ _ FR L16F LJF) | exact FRF]
      | unfold sql_lfacts, bit_ok; cbn [l_DST l_tLL l_tOF l_tML l_SEQ l_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact NX | exact HA1 | exact HV | exact HM | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] .. ])
      end.

  - (* [comment removed for export] *)
    destruct C as (C1 & C2). subst ptr.
    try hold TRANS. try hold ST0. try hold CONT. try hold HK. try hold L1. try hold L2. try hold L3. try hold L4. try hold L5. try hold L6. try hold En. try hold Esqb. try hold NX. try hold HV. try hold HM. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold S43. try hold S44. try hold S45. try hold S46. try hold S47. try hold S48. try hold S49. try hold S50. try hold S51. try hold S52. try hold S53. try hold S54. try hold S55. try hold S56. try hold S57. try hold S58. try hold S59. try hold S60. try hold S61. try hold S62. try hold S63. try hold S64. try hold S65. try hold S66. try hold S67. try hold S68. try hold S69. try hold S70. try hold S71. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoFLA (FR, FRF) [KAApp FRB 568; KAApp FF 256; KAUnp SEQ n] [0x8a860; 0x8ad30; 0x8ad3c; 0x8ad48] 480%nat
    [KZRange SPV 5056 (2^47); KZRange FRB 4096 (2^47); KZRange FF 6443008 (2^47); KZAlign SPV 16; KZAlign FF 8; KZRange (SEQ + n) 4097 (2^47 - 1);
     KZRange aLL 0 16; KZRange aML 0 16; KZRange aOF 0 31; KZRange SEQ 4096 (2^47 - 2); KZRange n 1 (2^47); KZRange bc 0 64;
     KZWr FRB 568; KZWr FF 256; KZDisj FF 256 FRB 568; KZDisj FRB 568 SEQ n; KZDisj FF 256 SEQ n]
    [(SEQ, n); (FRB, 568); (FF, 256)]
    [(FRB, 568); (FF, 256); (SEQ, n)].
    all: try clear DJ DJF DJR.
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]).
    all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
    all: try (lazymatch goal with |- sc_resid _ _ _ (SCDisj _ _ _ _) => kx_side_pre; try sql_oranges; try sql_bvr; try revert C'; try revert RGB; try revert RGA1; try revert RGA2; try revert RGA8; try revert RGC1; try revert RGC2; sql_clear_nonkx; intros; lia end).
    all: try sql_aclose.
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in ST0; try unfold held in CONT; try unfold held in HK; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in En; try unfold held in Esqb; try unfold held in NX; try unfold held in HV; try unfold held in HM; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
    all: lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8a860) _ _ _ _) => (eapply (CONT _ _ _ _ _ _ _ _ (Z_to_bv 64 0) _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) (Z_to_bv 64 0));
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact (sql_fr_ula _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ _ _ _ FR L16F LJF) | exact FRF]
      | unfold sql_lfacts, bit_ok; cbn [l_DST l_tLL l_tOF l_tML l_SEQ l_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact NX | exact HA1 | exact HV | exact HM | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] .. ])
      end.

  - (* [comment removed for export] *)
    destruct C as (C1 & C2 & C3).
    assert (QR : exists q r d, bc = 8 * q + r /\ ptr = SEQ + d /\ 0 <= q <= 8 /\ 0 <= r <= 7 /\ 8 <= d /\ d + 8 <= n)
      by (exists (bc / 8), (bc mod 8), (ptr - SEQ); clear - C1 C3 RS; lia).
    destruct QR as (q & r & d & -> & -> & Q1 & Q2 & Q3 & Q4).
    try hold TRANS. try hold ST0. try hold CONT. try hold HK. try hold L1. try hold L2. try hold L3. try hold L4. try hold L5. try hold L6. try hold En. try hold Esqb. try hold NX. try hold HV. try hold HM. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold S43. try hold S44. try hold S45. try hold S46. try hold S47. try hold S48. try hold S49. try hold S50. try hold S51. try hold S52. try hold S53. try hold S54. try hold S55. try hold S56. try hold S57. try hold S58. try hold S59. try hold S60. try hold S61. try hold S62. try hold S63. try hold S64. try hold S65. try hold S66. try hold S67. try hold S68. try hold S69. try hold S70. try hold S71. try hold OKLL. try hold OKOF. try hold OKML.
    kx_autoFLA (FR, FRF) [KAApp FRB 568; KAApp FF 256; KAUnp SEQ n] [0x8a860; 0x8ad30; 0x8ad3c; 0x8ad48] 480%nat
    [KZRange SPV 5056 (2^47); KZRange FRB 4096 (2^47); KZRange FF 6443008 (2^47); KZAlign SPV 16; KZAlign FF 8; KZRange (SEQ + n) 4097 (2^47 - 1);
     KZRange aLL 0 16; KZRange aML 0 16; KZRange aOF 0 31; KZRange SEQ 4096 (2^47 - 17); KZRange (SEQ + (-1 * q + d)) 4096 (2^47 - 9); KZRange (SEQ + d - q) 4096 (2^47 - 9); KZRange n 16 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange d 8 (2^47); KZRange (d - q) 0 (2^47); KZRange (n - d) 8 (2^47); KZRange (n - d + q) 8 (2^47);
     KZWr FRB 568; KZWr FF 256; KZDisj FF 256 FRB 568; KZDisj FRB 568 SEQ n; KZDisj FF 256 SEQ n]
    [(SEQ, n); (FRB, 568); (FF, 256)]
    [(FRB, 568); (FF, 256); (SEQ, n)].
    all: try clear DJ DJF DJR.
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]).
    all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
    all: try (lazymatch goal with |- sc_resid _ _ _ (SCDisj _ _ _ _) => kx_side_pre; try sql_oranges; try sql_bvr; try revert C'; try revert RGB; try revert RGA1; try revert RGA2; try revert RGA8; try revert RGC1; try revert RGC2; sql_clear_nonkx; intros; lia end).
    all: try sql_aclose.
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in ST0; try unfold held in CONT; try unfold held in HK; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in En; try unfold held in Esqb; try unfold held in NX; try unfold held in HV; try unfold held in HM; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
    all: lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8a860) _ _ _ _) => (eapply (CONT _ _ _ _ _ _ _ _ (Z_to_bv 64 0) _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) (Z_to_bv 64 0));
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact (sql_fr_ula _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ _ _ _ FR L16F LJF) | exact FRF]
      | unfold sql_lfacts, bit_ok; cbn [l_DST l_tLL l_tOF l_tML l_SEQ l_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact NX | exact HA1 | exact HV | exact HM | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] .. ])
      end.

  - (* [comment removed for export] *)
    destruct C as (C1 & C2 & C3 & C4).
    assert (QR : exists q r d, bc = 8 * q + r /\ ptr = SEQ + d /\ 0 <= q <= 8 /\ 0 <= r <= 7 /\ 1 <= d <= 7 /\ d + 8 <= n)
      by (exists (bc / 8), (bc mod 8), (ptr - SEQ); clear - C1 C3 C4 RS; lia).
    destruct QR as (q & r & d & -> & -> & Q1 & Q2 & Q3 & Q4).
    destruct (Z_le_gt_dec q d) as [QD|QD].
    + try hold TRANS. try hold ST0. try hold CONT. try hold HK. try hold L1. try hold L2. try hold L3. try hold L4. try hold L5. try hold L6. try hold En. try hold Esqb. try hold NX. try hold HV. try hold HM. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold S43. try hold S44. try hold S45. try hold S46. try hold S47. try hold S48. try hold S49. try hold S50. try hold S51. try hold S52. try hold S53. try hold S54. try hold S55. try hold S56. try hold S57. try hold S58. try hold S59. try hold S60. try hold S61. try hold S62. try hold S63. try hold S64. try hold S65. try hold S66. try hold S67. try hold S68. try hold S69. try hold S70. try hold S71. try hold OKLL. try hold OKOF. try hold OKML.
      kx_autoFLA (FR, FRF) [KAApp FRB 568; KAApp FF 256; KAUnp SEQ n] [0x8a860; 0x8ad30; 0x8ad3c; 0x8ad48] 480%nat
    [KZRange SPV 5056 (2^47); KZRange FRB 4096 (2^47); KZRange FF 6443008 (2^47); KZAlign SPV 16; KZAlign FF 8; KZRange (SEQ + n) 4097 (2^47 - 1);
     KZRange aLL 0 16; KZRange aML 0 16; KZRange aOF 0 31; KZRange SEQ 4096 (2^47 - 10); KZRange (SEQ + (-1 * q + d)) 4096 (2^47 - 9); KZRange (SEQ + d - q) 4096 (2^47 - 9); KZRange n 9 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange d 1 7; KZRange (d - q) 0 7; KZRange (n - d) 8 (2^47); KZRange (n - d + q) 8 (2^47);
     KZWr FRB 568; KZWr FF 256; KZDisj FF 256 FRB 568; KZDisj FRB 568 SEQ n; KZDisj FF 256 SEQ n]
    [(SEQ, n); (FRB, 568); (FF, 256)]
    [(FRB, 568); (FF, 256); (SEQ, n)].
    all: try clear DJ DJF DJR.
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]).
    all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
    all: try (lazymatch goal with |- sc_resid _ _ _ (SCDisj _ _ _ _) => kx_side_pre; try sql_oranges; try sql_bvr; try revert C'; try revert RGB; try revert RGA1; try revert RGA2; try revert RGA8; try revert RGC1; try revert RGC2; sql_clear_nonkx; intros; lia end).
    all: try sql_aclose.
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in ST0; try unfold held in CONT; try unfold held in HK; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in En; try unfold held in Esqb; try unfold held in NX; try unfold held in HV; try unfold held in HM; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
    all: lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8a860) _ _ _ _) => (eapply (CONT _ _ _ _ _ _ _ _ (Z_to_bv 64 0) _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) (Z_to_bv 64 0));
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact (sql_fr_ula _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ _ _ _ FR L16F LJF) | exact FRF]
      | unfold sql_lfacts, bit_ok; cbn [l_DST l_tLL l_tOF l_tML l_SEQ l_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact NX | exact HA1 | exact HV | exact HM | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] .. ])
      end.

    + try hold TRANS. try hold ST0. try hold CONT. try hold HK. try hold L1. try hold L2. try hold L3. try hold L4. try hold L5. try hold L6. try hold En. try hold Esqb. try hold NX. try hold HV. try hold HM. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold S43. try hold S44. try hold S45. try hold S46. try hold S47. try hold S48. try hold S49. try hold S50. try hold S51. try hold S52. try hold S53. try hold S54. try hold S55. try hold S56. try hold S57. try hold S58. try hold S59. try hold S60. try hold S61. try hold S62. try hold S63. try hold S64. try hold S65. try hold S66. try hold S67. try hold S68. try hold S69. try hold S70. try hold S71. try hold OKLL. try hold OKOF. try hold OKML.
      kx_autoFLA (FR, FRF) [KAApp FRB 568; KAApp FF 256; KAUnp SEQ n] [0x8a860; 0x8ad30; 0x8ad3c; 0x8ad48] 480%nat
    [KZRange SPV 5056 (2^47); KZRange FRB 4096 (2^47); KZRange FF 6443008 (2^47); KZAlign SPV 16; KZAlign FF 8; KZRange (SEQ + n) 4097 (2^47 - 1);
     KZRange aLL 0 16; KZRange aML 0 16; KZRange aOF 0 31; KZRange SEQ 4096 (2^47 - 10); KZRange n 9 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange d 1 7; KZRange (q - d) 1 8; KZRange (n - d) 8 (2^47);
     KZWr FRB 568; KZWr FF 256; KZDisj FF 256 FRB 568; KZDisj FRB 568 SEQ n; KZDisj FF 256 SEQ n]
    [(SEQ, n); (FRB, 568); (FF, 256)]
    [(FRB, 568); (FF, 256); (SEQ, n)].
    all: try clear DJ DJF DJR.
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]).
    all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
    all: try (lazymatch goal with |- sc_resid _ _ _ (SCDisj _ _ _ _) => kx_side_pre; try sql_oranges; try sql_bvr; try revert C'; try revert RGB; try revert RGA1; try revert RGA2; try revert RGA8; try revert RGC1; try revert RGC2; sql_clear_nonkx; intros; lia end).
    all: try sql_aclose.
    all: kx_mem.
    all: (try unfold held in TRANS; try unfold held in ST0; try unfold held in CONT; try unfold held in HK; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in En; try unfold held in Esqb; try unfold held in NX; try unfold held in HV; try unfold held in HM; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
    all: lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8a860) _ _ _ _) => (eapply (CONT _ _ _ _ _ _ _ _ (Z_to_bv 64 0) _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) (Z_to_bv 64 0));
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact (sql_fr_ula _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ _ _ _ FR L16F LJF) | exact FRF]
      | unfold sql_lfacts, bit_ok; cbn [l_DST l_tLL l_tOF l_tML l_SEQ l_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact NX | exact HA1 | exact HV | exact HM | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] .. ])
      end.

Qed.

End CANSEC1.
