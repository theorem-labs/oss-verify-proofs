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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_v_md AZ_seq_l_hkit AZ_seq_l_md_at.
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

Ltac sd_land ::=
  repeat match goal with
  | |- context [Z.land ?x ((2 ^ ?b + -1) mod 2 ^ 64)] =>
      let H := fresh "LND" in pose proof (land_mask_lt3 x b ltac:(lia)) as H;
      let v := fresh "lv" in set (v := Z.land x ((2 ^ b + -1) mod 2 ^ 64)) in *; clearbody v
  | _ : context [Z.land ?x ((2 ^ ?b + -1) mod 2 ^ 64)] |- _ =>
      let H := fresh "LND" in pose proof (land_mask_lt3 x b ltac:(lia)) as H;
      let v := fresh "lv" in set (v := Z.land x ((2 ^ b + -1) mod 2 ^ 64)) in *; clearbody v
  end.

Lemma md_update : forall P OEND LLO LEND LOCV K, sql_static P OEND LLO LEND LOCV -> 1 <= K <= l_nbSeq P ->
  md_upd P OEND LLO LEND LOCV K -> md_exec P OEND LLO LEND LOCV K -> md_rl1 P OEND LLO LEND LOCV K.
Proof.
  (* [comment removed for export] *)
  intros P OEND LLO LEND LOCV K ST HK  CONT1 CONT2 .
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  unfold md_rl1. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1].
  intros m1 c8 c16 c248 c264 c304 c312 c328 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP nLL aLL bLL vLL nOF bOF nML bML mlv ofs sn x6 x7 x10 x12 x27 x28 x30 INV LF NX HA1 HV HM HSN HS8 HRING.
  unfold md_upd in CONT1. unfold md_exec in CONT2.  cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in HK, CONT1, CONT2.
  pose proof (sql_linv_frame _ _ _ _ _ m1 c8 c16 (Z_to_bv 64 (DCTX + 30420)) (Z_to_bv 64 (DCTX + 30388)) (Z_to_bv 64 (DCTX + 95908)) (Z_to_bv 64 mlv) (Z_to_bv 64 ((DCTX + 30368) + 4)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (nbSeq - 1)) (Z_to_bv 64 1152921504606846976) c248 c264 c304 c312 ofs c328 (Z_to_bv 64 139648) c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV) as TRANS. cbn [sql_frame sql_ffr l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in TRANS.
  
  pose proof (sql_bm_asan _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (UBM & RBM & RBMS). cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in UBM, RBM, RBMS.
  pose proof (sql_loc_shadow _ _ _ _ _ m1 c8 c16 (Z_to_bv 64 (DCTX + 30420)) (Z_to_bv 64 (DCTX + 30388)) (Z_to_bv 64 (DCTX + 95908)) (Z_to_bv 64 mlv) (Z_to_bv 64 ((DCTX + 30368) + 4)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (nbSeq - 1)) (Z_to_bv 64 1152921504606846976) c248 c264 c304 c312 ofs c328 (Z_to_bv 64 139648) c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV) as (ZLBE & ZLOC & RLBE & RLOC & ED8 & RD8). cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in ZLBE, ZLOC, RLBE, RLOC, ED8, RD8.
  apply (sql_lopen_k _ _ _ _ _ m1 c8 c16 (Z_to_bv 64 (DCTX + 30420)) (Z_to_bv 64 (DCTX + 30388)) (Z_to_bv 64 (DCTX + 95908)) (Z_to_bv 64 mlv) (Z_to_bv 64 ((DCTX + 30368) + 4)) (Z_to_bv 64 0) (Z_to_bv 64 (OEND - 32)) (Z_to_bv 64 (nbSeq - 1)) (Z_to_bv 64 1152921504606846976) c248 c264 c304 c312 ofs c328 (Z_to_bv 64 139648) c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV); cbn [sql_ffr l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros jpad jseq FR FRF L16F LJF SQB MI UFL USEQ RSQ RSQS.
  apply sql_fr_vmd in FR. cbv delta [sql_ffr] in FRF. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in FR, FRF.
  pose proof LF as LF0. apply (sql_lf_k _ _ _ _ _ _ _ _ _ _ _ _ LF); cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros L1 L2 L3 L4 L5 L6 L7.
  apply (sql_rg_k _ _ _ _ _ ST); cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  unfold sql_next in NX. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in NX. pose proof NX as (NX1 & NX2 & NX3 & NX4 & NX5 & NX6 & NX7 & NX8 & NX9).
  rewrite <- (Z_to_bv_bv_unsigned ofs) in *. pose proof (kx_u64_range ofs) as HO. remember (bv_unsigned ofs) as ofz eqn:Eofz. clear Eofz ofs.
  sd_static_open ST. unfold held in RGB.
  pose proof (seq_pow_le _ _ OKLL) as PLL. pose proof (seq_pow_le _ _ OKOF) as POF. pose proof (seq_pow_le _ _ OKML) as PML.
  assert (RS : 0 <= bc <= 9900000 /\ 1 <= K <= 98047) by (clear - L6 HK S16; lia).
  assert (RP : 1 <= 2^bLL <= 512 /\ 1 <= 2^bOF <= 512 /\ 1 <= 2^bML <= 512 /\ nLL <= 511 /\ nOF <= 511 /\ nML <= 511).
  { clear - NX1 NX2 NX3 NX4 NX5 NX6 NX7 NX8 NX9 PLL POF PML.
    pose proof (Z.pow_pos_nonneg 2 bLL). pose proof (Z.pow_pos_nonneg 2 bOF). pose proof (Z.pow_pos_nonneg 2 bML). lia. }
  pose proof (bitmask_know m1 bLL MI ltac:(clear - NX1; lia)) as BK1.
  pose proof (bitmask_know m1 bOF MI ltac:(clear - NX4; lia)) as BK2.
  pose proof (bitmask_know m1 bML MI ltac:(clear - NX7; lia)) as BK3.
  unfold BITMASK in BK1, BK2, BK3.
  assert (MUL : munch [(FRB, FRB + 568); (FF, FF + 256)] m1 m1) by apply munch_refl. assert (WMl : wmono bsegs m1 m1) by apply wmono_refl.
  assert (PA : 0 < 2^aLL <= 65536) by (clear - HA1; split; [apply Z.pow_pos_nonneg; lia | change 65536 with (2^16); apply Z.pow_le_mono_r; lia]).
  assert (HV' : 0 <= vLL <= 131071) by (clear - HV; lia). assert (HM' : 0 <= mlv <= 262143) by (clear - HM; lia).
  
  assert (RSN : 8 <= sn <= 98046) by (clear - HSN HS8 HK S16; lia).
  try hold TRANS. try hold CONT1. try hold CONT2. try hold LF0. try hold NX. try hold HK. try hold L1. try hold L2. try hold L3. try hold L4. try hold L5. try hold L6. try hold L7. try hold NX3. try hold NX6. try hold NX9. try hold ZLBE. try hold RLBE. try hold ED8. try hold S1. try hold S2. try hold S3. try hold S4. try hold S5. try hold S6. try hold S7. try hold S8. try hold S9. try hold S10. try hold S11. try hold S12. try hold S13. try hold S14. try hold S15. try hold S16. try hold S18. try hold S19. try hold S20. try hold S21. try hold S22. try hold S23. try hold S24. try hold S25. try hold S26. try hold S27. try hold S28. try hold S29. try hold S30. try hold S31. try hold S32. try hold S33. try hold S34. try hold S35. try hold S36. try hold S37. try hold S38. try hold S39. try hold S40. try hold S41. try hold S42. try hold S43. try hold S44. try hold S45. try hold S46. try hold S47. try hold S48. try hold S49. try hold S50. try hold S51. try hold S52. try hold S53. try hold S54. try hold S55. try hold S56. try hold S57. try hold S58. try hold S59. try hold S60. try hold S61. try hold S62. try hold S63. try hold S64. try hold S65. try hold S66. try hold S67. try hold S68. try hold S69. try hold S70. try hold S71. try hold OKLL. try hold OKOF. try hold OKML.
  kx_autoFLA (FR, FRF) [KAApp FRB 568; KAApp FF 256; KAUnp 0x22180 128] [0x8b128; 0x8b288; 0x8ca10; 0x8ca24; 0x8ca38] 480%nat
    [KZRange SPV 5056 (2^47); KZRange FRB 4096 (2^47); KZRange FF 6443008 (2^47); KZAlign SPV 16; KZAlign FF 8; KZRange bc 0 9900000; KZRange K 1 98047; KZRange sn 8 98046; KZRange D8 512 17592186032416; KZWord (2147450880 + D8 + 3796) 1 0;
     KZRange nLL 0 511; KZRange nOF 0 511; KZRange nML 0 511; KZRange aLL 0 16; KZRange bLL 0 9; KZRange bOF 0 9; KZRange bML 0 9;
     KZRange vLL 0 131071; KZRange mlv 0 262143;
     KZRange (2^bLL) 1 512; KZRange (2^bOF) 1 512; KZRange (2^bML) 1 512;
     KZWord (BITMASK + 4 * bLL) 4 (2^bLL - 1); KZWord (BITMASK + 4 * bOF) 4 (2^bOF - 1); KZWord (BITMASK + 4 * bML) 4 (2^bML - 1);
     KZWr FRB 568; KZWr FF 256; KZDisj FF 256 FRB 568; KZImg 0x22180 0x22200]
    [(FRB, 568); (FF, 256)]
    [(FRB, 568); (FF, 256); (0x22180, 128); (2147450880 + D8 + 3796, 1)].
  all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
  all: try (lazymatch goal with |- sc_resid _ _ _ (SCDisj _ _ _ _) => kx_side_pre; try sql_oranges; try sql_bvr; try revert C'; try revert RGB; try revert RGA1; try revert RGA2; try revert RGA8; try revert RGC1; try revert RGC2; sql_clear_nonkx; intros; lia end).
  all: try sql_aclose.
  all: kx_mem.
  all: sd_rbf2.
  all: sd_land.
  all: (try unfold held in TRANS; try unfold held in CONT1; try unfold held in CONT2; try unfold held in LF0; try unfold held in NX; try unfold held in HK; try unfold held in L1; try unfold held in L2; try unfold held in L3; try unfold held in L4; try unfold held in L5; try unfold held in L6; try unfold held in L7; try unfold held in NX3; try unfold held in NX6; try unfold held in NX9; try unfold held in ZLBE; try unfold held in RLBE; try unfold held in ED8; try unfold held in S1; try unfold held in S2; try unfold held in S3; try unfold held in S4; try unfold held in S5; try unfold held in S6; try unfold held in S7; try unfold held in S8; try unfold held in S9; try unfold held in S10; try unfold held in S11; try unfold held in S12; try unfold held in S13; try unfold held in S14; try unfold held in S15; try unfold held in S16; try unfold held in S18; try unfold held in S19; try unfold held in S20; try unfold held in S21; try unfold held in S22; try unfold held in S23; try unfold held in S24; try unfold held in S25; try unfold held in S26; try unfold held in S27; try unfold held in S28; try unfold held in S29; try unfold held in S30; try unfold held in S31; try unfold held in S32; try unfold held in S33; try unfold held in S34; try unfold held in S35; try unfold held in S36; try unfold held in S37; try unfold held in S38; try unfold held in S39; try unfold held in S40; try unfold held in S41; try unfold held in S42; try unfold held in S43; try unfold held in S44; try unfold held in S45; try unfold held in S46; try unfold held in S47; try unfold held in S48; try unfold held in S49; try unfold held in S50; try unfold held in S51; try unfold held in S52; try unfold held in S53; try unfold held in S54; try unfold held in S55; try unfold held in S56; try unfold held in S57; try unfold held in S58; try unfold held in S59; try unfold held in S60; try unfold held in S61; try unfold held in S62; try unfold held in S63; try unfold held in S64; try unfold held in S65; try unfold held in S66; try unfold held in S67; try unfold held in S68; try unfold held in S69; try unfold held in S70; try unfold held in S71; try unfold held in OKLL; try unfold held in OKOF; try unfold held in OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
  all: first
    [ eapply CONT1 with (c352 := Z_to_bv 64 0);
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact (sql_fr_umd _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ _ _ _ FR L16F LJF) | exact FRF]
      | unfold sql_lfacts; cbn [l_DST l_tLL l_tOF l_tML l_SEQ l_sq];
        split; [exact L1|]; split; [exact L2|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [lia|];
        eapply bit_ok_mono; [exact L7 | lia]
      | exact HO | lia | lia | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] .. ]
    | eapply CONT2 with (c352 := Z_to_bv 64 0);
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact (sql_fr_umd _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ (Z_to_bv 64 0) _ _ (Z_to_bv 64 0) _ _ _ _ _ _ _ FR L16F LJF) | exact FRF]
      | eapply sql_lfacts_bc; [exact LF0 | lia]
      | exact HO | lia | lia  | first [eassumption | lia | apply land7 | (rewrite ?Z.mod_small by lia; reflexivity)] ..] ].
Qed.

End CANSEC1.
