(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 ZdCellKit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_hkit AZ_seq_l_ibase AZ_seq_l_iat AZ_seq_l_ikit AZ_seq_l_ickit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
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

Lemma sql_i3_ok : forall P OEND, sql_static P OEND (l_LITP P) (l_LBE P) (l_LOC P) -> zd_initfse_stmtA ->
  (l_LLT P + 4104 < 2^47 /\ l_OFT P + 2056 < 2^47 /\ l_MLT P + 4104 < 2^47) ->
  ai_I5 P OEND -> ai_I3 P OEND.
Proof.
  intros P OEND ST IFS TST CONT.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  cbv delta [ai_I3 sql_iregs sql_ifrI sql_imidA sql_iffC]. cbn [app l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1].
  intros m1 ja jb jc jd je jf jg jh ji jj jk jr jseq jpad j88 p0 p1 p2 cw A0 bc ptr sLL x5 x6 x7 x13 x14 x15 x16 x17 x25 x26 x27 x28 x29 x30 x31 INV EA0 HBC BOK HS1.
  subst A0.
  cbv delta [ai_I5 sql_iregs sql_ifrI sql_imidB sql_iffD] in CONT. cbn [app l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in CONT.
  (* [comment removed for export] *)
  pose proof INV as (FR0 & FRF0 & IREST).
  destruct (sql_cbst32 m1 FF [CB 32 jfh; C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 SEQ); C8 (Z_to_bv 64 (SEQ + 8)); C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (LLT + 8))] j88 [C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))] FRF0) as (u1 & u2 & j104 & FRF1).
  cbn [app] in FRF1.
  assert (INV1 : sql_iinv (mkSLQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1) OEND LITP LBE LOC m1 _ _) by (exact (conj FR0 (conj FRF1 IREST))).
  clear INV FR0 FRF0 FRF1 IREST.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (sql_initfse_ispec (mkSLQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1) OEND LITP LBE LOC m1 _ cw bc jpad ptr [C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (LLT + 8))] u1 u2 [CB 16 j104; C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))] OFT tOF K_OF 73 (FF + 88)
              (Z_to_bv 64 567424) x5 x6 x7 x13 x14 x15 x16 x17 (Z_to_bv 64 DST) (Z_to_bv 64 nbSeq) (Z_to_bv 64 2147450880) (Z_to_bv 64 DCTX) (Z_to_bv 64 (FF + 32)) x25 x26 x27 x28 x29 x30 x31);
      [ exact ST | exact IFS | exact INV1 | cbn [l_LLT l_OFT l_MLT l_tLL l_tOF l_tML]; right; left; split; [reflexivity | split; reflexivity] | exact TST
      | cbn [cells_size csize Nat.add length l_FF]; clear; lia | cbn [cells_size csize Nat.add length]; clear; lia | cbn [cells_size csize Nat.add length]; clear; lia
      | clear - HBC; lia | clear; lia | exact BOK ]. }
  clear INV1. cbv delta [sql_initfse_ipost sql_iregs]. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1].
  intros ms2 (m2 & cw2 & bc2 & jpad2 & ptr2 & sv & t0_ & t1_ & t2_ & a0_ & a1_ & a2_ & a3_ & a4_ & a5_ & a6_ & a7_ & t3_ & t4_ & t5_ & t6_ & -> & INV2 & HST & HBC2 & BOK2).
  replace (ret_pc (Z_to_bv 64 567424)) with (Z_to_bv 64 567424) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  cbv delta [sbd_cells] in INV2. cbn [app] in INV2.
  pose proof (sql_iinv_frame _ _ _ _ _ m2 _ _ ST INV2) as TRANS. cbn [l_FRB l_FF] in TRANS.
  apply (sql_iopen_k _ _ _ _ _ _ _ _ ST INV2); cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros FR FRF PT SQB MI UFL USEQ RSQ RSQS UD RD RDS.
  apply (sql_rg_k _ _ _ _ _ ST); cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  pose proof ST as ST0. sd_static_open ST. unfold held in RGB.
  unfold dctx_ptrs in PT. unfold DCTX_SIZEOF in UD, RD, RDS.
  assert (MUL : munch [(FRB, FRB + 632); (FF, FF + 256)] m2 m2) by apply munch_refl. assert (WMl : wmono bsegs m2 m2) by apply wmono_refl.
  assert (RG : 4096 <= OEND < 2^47 /\ 0 <= D8 /\ 8 * D8 + 95992 < 2^47 /\ 4096 <= DCTX /\ DCTX + 95992 < 2^47 /\ 4096 <= DST < 2^47 /\ DCTX = 8 * D8 /\
               4096 <= LLT /\ LLT + 4104 <= 2^47 /\ 4096 <= OFT /\ OFT + 2056 <= 2^47 /\ 4096 <= MLT /\ MLT + 4104 <= 2^47 /\ 1 <= nbSeq <= 98047 /\ 4096 <= PFX <= DST)
    by (unfold held in S70; clear - S1 S2 S3 S4 S5 S6 S7 S16 S19 S20 S21 S22 S23 S61 S70; destruct S61 as (_ & _ & _ & _ & ED8 & _); lia).
  destruct RG as (RG1 & RG2 & RG3 & RG4 & RG5 & RG6 & ED8 & RG7 & RG8 & RG9 & RG10 & RG11 & RG12 & RG13 & RG14).
  assert (DJD1 : FRB + 632 <= DCTX \/ DCTX + 95992 <= FRB) by (unfold held in S27; clear - S27 S18 S47; lia).
  assert (DJD2 : FF + 256 <= DCTX \/ DCTX + 95992 <= FF) by (unfold held in S54; clear - S54; lia).
  clear SQB UFL USEQ RSQ RSQS.
  hold CONT. hold HBC2. hold BOK2. hold HST. hold HS1. hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold S9. hold S10. hold S11. hold S12. hold S13. hold S14. hold S15. hold S16. hold S18. hold S19. hold S20. hold S21. hold S22. hold S23. hold S24. hold S25. hold S26. hold S27. hold S28. hold S29. hold S30. hold S31. hold S32. hold S33. hold S34. hold S35. hold S36. hold S37. hold S38. hold S39. hold S40. hold S41. hold S42. hold S43. hold S44. hold S45. hold S46. hold S47. hold S48. hold S49. hold S50. hold S51. hold S52. hold S53. hold S54. hold S55. hold S56. hold S57. hold S58. hold S59. hold S60. hold S61. hold S62. hold S63. hold S64. hold S65. hold S66. hold S67. hold S68. hold S69. hold S70. hold S71. hold OKLL. hold OKOF. hold OKML. hold OKLL. hold OKOF. hold OKML.
  kx_autoFLA (FR, FRF, PT) [KAApp FRB 632; KAApp FF 256; KAUnp DCTX 95992] [0x96148] 40%nat
    [KZRange SPV 5056 (2^47); KZRange FRB 4096 (2^47); KZRange FF 6459392 (2^47); KZAlign SPV 16; KZAlign FF 8;
     KZRange OEND 4096 (2^47); KZRange D8 0 (2^44); KZRange DCTX 4096 (2^47 - 95992); KZAlign DCTX 8; KZRange DST 4096 (2^47); KZRange PFX 4096 (2^47);
     KZRange LLT 4096 (2^47 - 4104); KZRange OFT 4096 (2^47 - 2056); KZRange MLT 4096 (2^47 - 4104); KZRange nbSeq 1 98047; KZRange (Z.min nbSeq 8) 1 8;
     KZWr FRB 632; KZWr FF 256; KZDisj FF 256 FRB 632; KZDisj FRB 632 DCTX 95992; KZDisj FF 256 DCTX 95992]
    [(FRB, 632); (FF, 256)]
    [(FRB, 632); (FF, 256); (DCTX, 32)].
  all: try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 588632) _ _ _ _) => kx_trap_fast end).
  all: try (lazymatch goal with |- sc_resid _ _ _ (SCDisj _ _ _ _) => kx_side_pre; try sql_oranges; try sql_bvr; try revert C'; try revert RGB; try revert RGA1; try revert RGA2; try revert RGA8; try revert RGC1; try revert RGC2; sql_clear_nonkx; intros; lia end).
  all: try sql_aclose.
  all: kx_mem.
  all: (unfold held in CONT, HBC2, BOK2, HST, HS1, S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, OKLL, OKOF, OKML, OKLL, OKOF, OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => kx_z end).
  all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x96148) _ _ _ _) =>
        (eapply CONT;
         [ eapply sql_iinv_eq2; [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR | exact FRF] | cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; sql_cells_eq | cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; reflexivity ]
         | clear; lia
         | clear - HBC2; lia
         | exact BOK2 | exact HS1
         | exact HST ])
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?UPC) _ _ _ _) => fail 99 "unexpected LEAF, pc =" UPC
    | |- ?UNEXPECTED => fail 99 "unexpected goal:" UNEXPECTED
    end.
Qed.

End CANSEC1.
