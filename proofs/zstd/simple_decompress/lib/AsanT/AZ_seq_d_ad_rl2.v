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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_seq_kit AZ_seq_gkit AZ_seq_d_base AZ_seq_d_lbase AZ_seq_d_lkit AZ_seq_d_akit AZ_seq_d_okit AZ_seq_d_ad_at.
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

Lemma ad_reload2 : forall P OEND LLO LEND LOCV K, sqd_static P OEND LLO LEND LOCV -> 1 <= K <= w_nbSeq P ->
  ad_exec P OEND LLO LEND LOCV K -> ad_execb P OEND LLO LEND LOCV K -> ad_slow P OEND LLO LEND LOCV K -> ad_upd P OEND LLO LEND LOCV K.
Proof.
  (* [comment removed for export] *)
  intros P OEND LLO LEND LOCV K ST HK  CONT CONTB CONTS.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  unfold ad_upd. cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1].
  intros m1 c24 c32 c40 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP llv mlv ofs x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x22 x28 x29 x30 INV LF HO HLV HMV.
  unfold ad_exec in CONT. unfold ad_execb in CONTB. unfold ad_slow in CONTS. cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in HK, CONT, CONTB, CONTS.
  pose proof (sqd_linv_frame _ _ _ _ _ m1 c24 c32 c40 (Z_to_bv 64 LEND) c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as TRANS. cbn [sqd_frame sqd_ffr w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in TRANS.
  
  apply (sqd_lopen_k _ _ _ _ _ m1 c24 c32 c40 (Z_to_bv 64 LEND) c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV); cbn [sqd_frame sqd_ffr w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1]; intros jpad jseq FR FRF L16F LJF SQB MI UFL USEQ RSQ RSQS.
  cbv delta [sqd_frame sqd_ffr] in FR, FRF. cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1] in FR, FRF.
  apply (sqd_lf_k _ _ _ _ _ _ _ _ _ _ _ _ LF); cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1]; intros L1 L2 L3 L4 L5 L6 L7.
  apply (sqd_rg_k _ _ _ _ _ ST); cbn [w_ra w_gp w_tp w_s0 w_s1 w_s2 w_s3 w_s4 w_s5 w_s6 w_s7 w_s8 w_s9 w_s10 w_s11 w_F w_fc w_m w_SPV w_lo w_DCTX w_DST w_CAP w_B0 w_B1 w_SEQ w_nbSeq w_LLT w_MLT w_OFT w_PFX w_LITP w_LITSZ w_LITB w_LOC w_sq w_tLL w_tOF w_tML w_huf w_r0 w_r1 w_r2 w_pde w_dend w_expd w_pcs w_dsz w_bt w_stg w_le w_fe w_ws w_AI w_fflag w_L w_RNG w_st w_LB w_m0 w_FRB w_FF w_SHF w_D8 w_j0 w_j224 w_jfh w_j144 w_jsh0 w_jsh1]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  pose proof ST as ST0. sd_static_open ST. unfold held in RGB.
  remember (map (Z_to_bv 8) sq) as sqb eqn:Esqb. remember (zlen sq) as n eqn:En. try rewrite <- En in USEQ. try rewrite <- En in RSQ. try rewrite <- En in RSQS.
  assert (DJF : FF + 256 <= SEQ \/ SEQ + n <= FF) by (unfold held in S56; clear - S56 En; lia). assert (DJR : FRB + 216 <= SEQ \/ SEQ + n <= FRB) by (unfold held in S25; clear - S25 S18 S47 En; lia).
  assert (LSQ : Z.of_nat (length sqb) = n) by (subst sqb n; rewrite length_map; reflexivity).
  assert (MUL : munch [(FRB, FRB + 216); (FF, FF + 256)] m1 m1) by apply munch_refl. assert (WMl : wmono bsegs m1 m1) by apply wmono_refl.
  assert (RS : 0 <= bc <= 9900000) by (clear - L6 HK S16; lia).
  assert (DJ : SPV - 216 + 216 <= SEQ \/ SEQ + n <= SPV - 216) by (unfold held in S25; clear - S25 S18; lia). clear DJ.
  assert (RGL : 4096 <= LP < 2^47 /\ 4096 <= LEND < 2^47 /\ 0 <= llv <= 262143) by (clear - L2 S8 S9 S11 HLV; lia).
  assert (CASES : 65 <= bc \/ (bc <= 64 /\ ptr = SEQ) \/ (bc <= 64 /\ 8 <= n /\ SEQ + 8 <= ptr <= SEQ + n - 8) \/
                  (bc <= 64 /\ 8 <= n /\ SEQ + 1 <= ptr <= SEQ + 7 /\ ptr <= SEQ + n - 8)).
  { unfold bit_ok in L7. clear - L7. destruct (Z_le_gt_dec bc 64) as [B|B]; [|left; lia]. destruct (L7 B) as [E|(N8 & R)]; [right; left; lia|].
    destruct (Z_le_gt_dec (SEQ + 8) ptr); [right; right; left; lia|]. destruct (Z.eq_dec ptr SEQ); [right; left; lia| right; right; right; lia]. }
  clear L7.
  destruct CASES as [C|[C|[C|C]]].
  - (* [comment removed for export] *)
    hold TRANS. hold ST0. hold CONT. hold CONTB. hold CONTS. hold HK. hold L1. hold L2. hold L3. hold L4. hold L5. hold L6. hold En. hold Esqb. hold HO. hold HLV. hold HMV. hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold S9. hold S10. hold S11. hold S12. hold S16. hold S18. hold S19. hold S20. hold S21. hold S22. hold S23. hold S24. hold S25. hold S26. hold S27. hold S28. hold S29. hold S30. hold S31. hold S32. hold S33. hold S34. hold S35. hold S36. hold S37. hold S38. hold S39. hold S40. hold S41. hold S42. hold S43. hold S44. hold S45. hold S46. hold S47. hold S48. hold S49. hold S50. hold S51. hold S52. hold S53. hold S54. hold S55. hold S56. hold S57. hold S58. hold S59. hold S60. hold S61. hold S62. hold S63. hold S64. hold S65. hold S66. hold S67. hold S68. hold S69. hold OKLL. hold OKOF. hold OKML.
    kx_autoFLA (FR, FRF) [KAApp FRB 216; KAApp FF 256; KAUnp SEQ n] [0x93d44; 0x93d50; 0x9414c; 0x9461c; 0x94604; 0x94610] 480%nat
    [KZRange SPV 4704 (2^47); KZRange FRB 4096 (2^47); KZRange FF 6443008 (2^47); KZAlign SPV 16; KZRange (SEQ + n) 4097 (2^47 - 1);
     KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange llv 0 262143; KZRange SEQ 4096 (2^47 - 2); KZRange n 1 (2^47); KZRange bc 65 9900000;
     KZWr FRB 216; KZWr FF 256; KZDisj FF 256 FRB 216; KZDisj FRB 216 SEQ n; KZDisj FF 256 SEQ n]
    [(SEQ, n); (FRB, 216); (FF, 256)]
    [(FRB, 216); (FF, 256); (SEQ, n)].
    all: try clear DJ DJF DJR.
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]).
    all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
    all: try sqd_aclose.
    all: kx_mem.
    all: (unfold held in TRANS, ST0, CONT, CONTB, CONTS, HK, L1, L2, L3, L4, L5, L6, En, Esqb, HO, HLV, HMV, S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, OKLL, OKOF, OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
    all: lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x93d44) _ _ _ _) => (eapply (CONT _ _ c32 c40);
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF]
      | unfold sqd_lfacts, bit_ok; cbn [w_DST w_tLL w_tOF w_tML w_SEQ w_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact HO | exact HLV | exact HMV ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x93d50) _ _ _ _) => (eapply (CONTB _ _ c32 c40);
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF]
      | unfold sqd_lfacts, bit_ok; cbn [w_DST w_tLL w_tOF w_tML w_SEQ w_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact HO | exact HLV | exact HMV | lia | lia ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9414c) _ _ _ _) => (eapply (CONTS _ _ c32 c40);
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF]
      | unfold sqd_lfacts, bit_ok; cbn [w_DST w_tLL w_tOF w_tML w_SEQ w_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact HO | exact HLV | exact HMV ])
      end.

  - (* [comment removed for export] *)
    destruct C as (C1 & C2). subst ptr.
    hold TRANS. hold ST0. hold CONT. hold CONTB. hold CONTS. hold HK. hold L1. hold L2. hold L3. hold L4. hold L5. hold L6. hold En. hold Esqb. hold HO. hold HLV. hold HMV. hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold S9. hold S10. hold S11. hold S12. hold S16. hold S18. hold S19. hold S20. hold S21. hold S22. hold S23. hold S24. hold S25. hold S26. hold S27. hold S28. hold S29. hold S30. hold S31. hold S32. hold S33. hold S34. hold S35. hold S36. hold S37. hold S38. hold S39. hold S40. hold S41. hold S42. hold S43. hold S44. hold S45. hold S46. hold S47. hold S48. hold S49. hold S50. hold S51. hold S52. hold S53. hold S54. hold S55. hold S56. hold S57. hold S58. hold S59. hold S60. hold S61. hold S62. hold S63. hold S64. hold S65. hold S66. hold S67. hold S68. hold S69. hold OKLL. hold OKOF. hold OKML.
    kx_autoFLA (FR, FRF) [KAApp FRB 216; KAApp FF 256; KAUnp SEQ n] [0x93d44; 0x93d50; 0x9414c; 0x9461c; 0x94604; 0x94610] 480%nat
    [KZRange SPV 4704 (2^47); KZRange FRB 4096 (2^47); KZRange FF 6443008 (2^47); KZAlign SPV 16; KZRange (SEQ + n) 4097 (2^47 - 1);
     KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange llv 0 262143; KZRange SEQ 4096 (2^47 - 2); KZRange n 1 (2^47); KZRange bc 0 64;
     KZWr FRB 216; KZWr FF 256; KZDisj FF 256 FRB 216; KZDisj FRB 216 SEQ n; KZDisj FF 256 SEQ n]
    [(SEQ, n); (FRB, 216); (FF, 256)]
    [(FRB, 216); (FF, 256); (SEQ, n)].
    all: try clear DJ DJF DJR.
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]).
    all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
    all: try sqd_aclose.
    all: kx_mem.
    all: (unfold held in TRANS, ST0, CONT, CONTB, CONTS, HK, L1, L2, L3, L4, L5, L6, En, Esqb, HO, HLV, HMV, S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, OKLL, OKOF, OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
    all: lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x93d44) _ _ _ _) => (eapply (CONT _ _ c32 c40);
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF]
      | unfold sqd_lfacts, bit_ok; cbn [w_DST w_tLL w_tOF w_tML w_SEQ w_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact HO | exact HLV | exact HMV ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x93d50) _ _ _ _) => (eapply (CONTB _ _ c32 c40);
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF]
      | unfold sqd_lfacts, bit_ok; cbn [w_DST w_tLL w_tOF w_tML w_SEQ w_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact HO | exact HLV | exact HMV | lia | lia ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9414c) _ _ _ _) => (eapply (CONTS _ _ c32 c40);
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF]
      | unfold sqd_lfacts, bit_ok; cbn [w_DST w_tLL w_tOF w_tML w_SEQ w_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact HO | exact HLV | exact HMV ])
      end.

  - (* [comment removed for export] *)
    destruct C as (C1 & C2 & C3).
    assert (QR : exists q r d, bc = 8 * q + r /\ ptr = SEQ + d /\ 0 <= q <= 8 /\ 0 <= r <= 7 /\ 8 <= d /\ d + 8 <= n)
      by (exists (bc / 8), (bc mod 8), (ptr - SEQ); clear - C1 C3 RS; lia).
    destruct QR as (q & r & d & -> & -> & Q1 & Q2 & Q3 & Q4).
    hold TRANS. hold ST0. hold CONT. hold CONTB. hold CONTS. hold HK. hold L1. hold L2. hold L3. hold L4. hold L5. hold L6. hold En. hold Esqb. hold HO. hold HLV. hold HMV. hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold S9. hold S10. hold S11. hold S12. hold S16. hold S18. hold S19. hold S20. hold S21. hold S22. hold S23. hold S24. hold S25. hold S26. hold S27. hold S28. hold S29. hold S30. hold S31. hold S32. hold S33. hold S34. hold S35. hold S36. hold S37. hold S38. hold S39. hold S40. hold S41. hold S42. hold S43. hold S44. hold S45. hold S46. hold S47. hold S48. hold S49. hold S50. hold S51. hold S52. hold S53. hold S54. hold S55. hold S56. hold S57. hold S58. hold S59. hold S60. hold S61. hold S62. hold S63. hold S64. hold S65. hold S66. hold S67. hold S68. hold S69. hold OKLL. hold OKOF. hold OKML.
    kx_autoFLA (FR, FRF) [KAApp FRB 216; KAApp FF 256; KAUnp SEQ n] [0x93d44; 0x93d50; 0x9414c; 0x9461c; 0x94604; 0x94610] 480%nat
    [KZRange SPV 4704 (2^47); KZRange FRB 4096 (2^47); KZRange FF 6443008 (2^47); KZAlign SPV 16; KZRange (SEQ + n) 4097 (2^47 - 1);
     KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange llv 0 262143; KZRange SEQ 4096 (2^47 - 17); KZRange (SEQ + (-1 * q + d)) 4096 (2^47 - 9); KZRange (SEQ + d - q) 4096 (2^47 - 9); KZRange n 16 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange d 8 (2^47); KZRange (d - q) 0 (2^47); KZRange (n - d) 8 (2^47); KZRange (n - d + q) 8 (2^47);
     KZWr FRB 216; KZWr FF 256; KZDisj FF 256 FRB 216; KZDisj FRB 216 SEQ n; KZDisj FF 256 SEQ n]
    [(SEQ, n); (FRB, 216); (FF, 256)]
    [(FRB, 216); (FF, 256); (SEQ, n)].
    all: try clear DJ DJF DJR.
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]).
    all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
    all: try sqd_aclose.
    all: kx_mem.
    all: (unfold held in TRANS, ST0, CONT, CONTB, CONTS, HK, L1, L2, L3, L4, L5, L6, En, Esqb, HO, HLV, HMV, S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, OKLL, OKOF, OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
    all: lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x93d44) _ _ _ _) => (eapply (CONT _ _ c32 c40);
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF]
      | unfold sqd_lfacts, bit_ok; cbn [w_DST w_tLL w_tOF w_tML w_SEQ w_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact HO | exact HLV | exact HMV ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x93d50) _ _ _ _) => (eapply (CONTB _ _ c32 c40);
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF]
      | unfold sqd_lfacts, bit_ok; cbn [w_DST w_tLL w_tOF w_tML w_SEQ w_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact HO | exact HLV | exact HMV | lia | lia ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9414c) _ _ _ _) => (eapply (CONTS _ _ c32 c40);
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF]
      | unfold sqd_lfacts, bit_ok; cbn [w_DST w_tLL w_tOF w_tML w_SEQ w_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact HO | exact HLV | exact HMV ])
      end.

  - (* [comment removed for export] *)
    destruct C as (C1 & C2 & C3 & C4).
    assert (QR : exists q r d, bc = 8 * q + r /\ ptr = SEQ + d /\ 0 <= q <= 8 /\ 0 <= r <= 7 /\ 1 <= d <= 7 /\ d + 8 <= n)
      by (exists (bc / 8), (bc mod 8), (ptr - SEQ); clear - C1 C3 C4 RS; lia).
    destruct QR as (q & r & d & -> & -> & Q1 & Q2 & Q3 & Q4).
    destruct (Z_le_gt_dec q d) as [QD|QD].
    + hold TRANS. hold ST0. hold CONT. hold CONTB. hold CONTS. hold HK. hold L1. hold L2. hold L3. hold L4. hold L5. hold L6. hold En. hold Esqb. hold HO. hold HLV. hold HMV. hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold S9. hold S10. hold S11. hold S12. hold S16. hold S18. hold S19. hold S20. hold S21. hold S22. hold S23. hold S24. hold S25. hold S26. hold S27. hold S28. hold S29. hold S30. hold S31. hold S32. hold S33. hold S34. hold S35. hold S36. hold S37. hold S38. hold S39. hold S40. hold S41. hold S42. hold S43. hold S44. hold S45. hold S46. hold S47. hold S48. hold S49. hold S50. hold S51. hold S52. hold S53. hold S54. hold S55. hold S56. hold S57. hold S58. hold S59. hold S60. hold S61. hold S62. hold S63. hold S64. hold S65. hold S66. hold S67. hold S68. hold S69. hold OKLL. hold OKOF. hold OKML.
      kx_autoFLA (FR, FRF) [KAApp FRB 216; KAApp FF 256; KAUnp SEQ n] [0x93d44; 0x93d50; 0x9414c; 0x9461c; 0x94604; 0x94610] 480%nat
    [KZRange SPV 4704 (2^47); KZRange FRB 4096 (2^47); KZRange FF 6443008 (2^47); KZAlign SPV 16; KZRange (SEQ + n) 4097 (2^47 - 1);
     KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange llv 0 262143; KZRange SEQ 4096 (2^47 - 10); KZRange (SEQ + (-1 * q + d)) 4096 (2^47 - 9); KZRange (SEQ + d - q) 4096 (2^47 - 9); KZRange n 9 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange d 1 7; KZRange (d - q) 0 7; KZRange (n - d) 8 (2^47); KZRange (n - d + q) 8 (2^47);
     KZWr FRB 216; KZWr FF 256; KZDisj FF 256 FRB 216; KZDisj FRB 216 SEQ n; KZDisj FF 256 SEQ n]
    [(SEQ, n); (FRB, 216); (FF, 256)]
    [(FRB, 216); (FF, 256); (SEQ, n)].
    all: try clear DJ DJF DJR.
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]).
    all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
    all: try sqd_aclose.
    all: kx_mem.
    all: (unfold held in TRANS, ST0, CONT, CONTB, CONTS, HK, L1, L2, L3, L4, L5, L6, En, Esqb, HO, HLV, HMV, S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, OKLL, OKOF, OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
    all: lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x93d44) _ _ _ _) => (eapply (CONT _ _ c32 c40);
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF]
      | unfold sqd_lfacts, bit_ok; cbn [w_DST w_tLL w_tOF w_tML w_SEQ w_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact HO | exact HLV | exact HMV ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x93d50) _ _ _ _) => (eapply (CONTB _ _ c32 c40);
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF]
      | unfold sqd_lfacts, bit_ok; cbn [w_DST w_tLL w_tOF w_tML w_SEQ w_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact HO | exact HLV | exact HMV | lia | lia ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9414c) _ _ _ _) => (eapply (CONTS _ _ c32 c40);
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF]
      | unfold sqd_lfacts, bit_ok; cbn [w_DST w_tLL w_tOF w_tML w_SEQ w_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact HO | exact HLV | exact HMV ])
      end.

    + hold TRANS. hold ST0. hold CONT. hold CONTB. hold CONTS. hold HK. hold L1. hold L2. hold L3. hold L4. hold L5. hold L6. hold En. hold Esqb. hold HO. hold HLV. hold HMV. hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold S9. hold S10. hold S11. hold S12. hold S16. hold S18. hold S19. hold S20. hold S21. hold S22. hold S23. hold S24. hold S25. hold S26. hold S27. hold S28. hold S29. hold S30. hold S31. hold S32. hold S33. hold S34. hold S35. hold S36. hold S37. hold S38. hold S39. hold S40. hold S41. hold S42. hold S43. hold S44. hold S45. hold S46. hold S47. hold S48. hold S49. hold S50. hold S51. hold S52. hold S53. hold S54. hold S55. hold S56. hold S57. hold S58. hold S59. hold S60. hold S61. hold S62. hold S63. hold S64. hold S65. hold S66. hold S67. hold S68. hold S69. hold OKLL. hold OKOF. hold OKML.
      kx_autoFLA (FR, FRF) [KAApp FRB 216; KAApp FF 256; KAUnp SEQ n] [0x93d44; 0x93d50; 0x9414c; 0x9461c; 0x94604; 0x94610] 480%nat
    [KZRange SPV 4704 (2^47); KZRange FRB 4096 (2^47); KZRange FF 6443008 (2^47); KZAlign SPV 16; KZRange (SEQ + n) 4097 (2^47 - 1);
     KZRange LP 4096 (2^47); KZRange LEND 4096 (2^47); KZRange llv 0 262143; KZRange SEQ 4096 (2^47 - 10); KZRange n 9 (2^47); KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange d 1 7; KZRange (q - d) 1 8; KZRange (n - d) 8 (2^47);
     KZWr FRB 216; KZWr FF 256; KZDisj FF 256 FRB 216; KZDisj FRB 216 SEQ n; KZDisj FF 256 SEQ n]
    [(SEQ, n); (FRB, 216); (FF, 256)]
    [(FRB, 216); (FF, 256); (SEQ, n)].
    all: try clear DJ DJF DJR.
    all: try (lazymatch goal with |- sc_resid _ _ _ _ => idtac end; first [kx_rd SQB | kx_z]).
    all: try (split; [lia | split; [lia | split; [lia | assumption]]]).
    all: try sqd_aclose.
    all: kx_mem.
    all: (unfold held in TRANS, ST0, CONT, CONTB, CONTS, HK, L1, L2, L3, L4, L5, L6, En, Esqb, HO, HLV, HMV, S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, OKLL, OKOF, OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
    all: lazymatch goal with
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x93d44) _ _ _ _) => (eapply (CONT _ _ c32 c40);
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF]
      | unfold sqd_lfacts, bit_ok; cbn [w_DST w_tLL w_tOF w_tML w_SEQ w_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact HO | exact HLV | exact HMV ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x93d50) _ _ _ _) => (eapply (CONTB _ _ c32 c40);
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF]
      | unfold sqd_lfacts, bit_ok; cbn [w_DST w_tLL w_tOF w_tML w_SEQ w_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact HO | exact HLV | exact HMV | lia | lia ])
      | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x9414c) _ _ _ _) => (eapply (CONTS _ _ c32 c40);
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF]
      | unfold sqd_lfacts, bit_ok; cbn [w_DST w_tLL w_tOF w_tML w_SEQ w_sq]; rewrite <- En;
        split; [exact L1|]; split; [exact L2|]; split; [exact L3|]; split; [exact L4|]; split; [exact L5|]; split; [lia|]; intros; lia
      | exact HO | exact HLV | exact HMV ])
      end.

Qed.

End CANSEC1.
