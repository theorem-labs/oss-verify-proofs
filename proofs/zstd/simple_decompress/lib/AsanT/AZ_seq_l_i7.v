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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_hkit AZ_seq_l_ibase AZ_seq_l_iat AZ_seq_l_ikit AZ_seq_l_xat AZ_seq_l_la_at.
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

(* [comment removed for export] *)
Local Ltac cells_at n H :=
  lazymatch type of H with rw_cells ?sg ?mm ?A ?cl => rewrite <- (firstn_skipn n cl) in H; cbn [firstn skipn] in H end.

Section CANSEC1. Context {rc : runConstT}.

Lemma sql_i7_ok : forall P OEND, sql_static P OEND (l_LITP P) (l_LBE P) (l_LOC P) ->
  la_head P OEND (l_LITP P) (l_LBE P) (l_LOC P) (l_nbSeq P) -> ai_I7 P OEND.
Proof.
  intros P OEND ST CONT.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  cbv delta [ai_I7 sql_iregsB sql_ifrB sql_ffr]. cbn [app l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1].
  intros m1 ja jb jc jd jf jg ji jr jseq jpad p0 p1 p2 cw bc ptr sLL sOF sML x1 x6 x7 x10 x12 x13 x14 x15 x17 x30 INV HBC BOK HS1 HS2 HS3.
  unfold la_head in CONT. cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in CONT.
  pose proof (sql_iinv_frame _ _ _ _ _ m1 _ _ ST INV) as TRANS. cbn [l_FRB l_FF] in TRANS.
  apply (sql_iopen_k _ _ _ _ _ _ _ _ ST INV); cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros FR FRF PT SQB MI UFL USEQ RSQ RSQS UD RD RDS.
  apply (sql_rg_k _ _ _ _ _ ST); cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; intros RGA1 RGA2 RGA3 RGA4 RGA5 RGA6 RGA7 RGA8 RGB RSTK RFF RSHF RGC1 RGC2.
  sd_static_open ST. unfold held in RGB.
  assert (MUL : munch [(FRB, FRB + 568); (FF, FF + 256)] m1 m1) by apply munch_refl. assert (WMl : wmono bsegs m1 m1) by apply wmono_refl.
  assert (RG : 4096 <= OEND < 2^47 /\ 4096 <= MLT /\ MLT + 4104 <= 2^47 /\ 0 <= D8 /\ 8 * D8 + 95992 < 2^47 /\ 4096 <= DCTX /\ DCTX + 95992 < 2^47 /\ 4096 <= DST < 2^47 /\
               1 <= nbSeq <= 98047 /\ 1 <= Z.min nbSeq 8 <= 8 /\ 4096 <= PFX <= DST /\ 4096 <= LBE < 2^47)
    by (unfold held in S70; clear - S1 S2 S3 S4 S5 S6 S7 S16 S19 S20 S23 S61 S70; destruct S61 as (_ & _ & _ & _ & ED8 & _); lia).
  destruct RG as (RG1 & RG2 & RG3 & RG4 & RG5 & RG6 & RG7 & RG8 & RG9 & RG10 & RG11 & RG12).
  clear PT SQB UFL USEQ RSQ RSQS UD RD RDS.
  hold TRANS. hold CONT. hold HBC. hold BOK. hold HS1. hold HS2. hold HS3. hold S1. hold S2. hold S3. hold S4. hold S5. hold S6. hold S7. hold S8. hold S9. hold S10. hold S11. hold S12. hold S13. hold S14. hold S15. hold S16. hold S18. hold S19. hold S20. hold S21. hold S22. hold S23. hold S24. hold S25. hold S26. hold S27. hold S28. hold S29. hold S30. hold S31. hold S32. hold S33. hold S34. hold S35. hold S36. hold S37. hold S38. hold S39. hold S40. hold S41. hold S42. hold S43. hold S44. hold S45. hold S46. hold S47. hold S48. hold S49. hold S50. hold S51. hold S52. hold S53. hold S54. hold S55. hold S56. hold S57. hold S58. hold S59. hold S60. hold S61. hold S62. hold S63. hold S64. hold S65. hold S66. hold S67. hold S68. hold S69. hold S70. hold S71. hold OKLL. hold OKOF. hold OKML. hold OKLL. hold OKOF. hold OKML.
  kx_autoFLA (FR, FRF) [KAApp FRB 568; KAApp FF 256] [0x8a6b0] 40%nat
    [KZRange SPV 5056 (2^47); KZRange FRB 4096 (2^47); KZRange FF 6443008 (2^47); KZAlign SPV 16; KZAlign FF 8;
     KZRange OEND 4096 (2^47); KZRange MLT 4096 (2^47 - 4104); KZRange D8 0 (2^44); KZRange DCTX 4096 (2^47 - 95992); KZRange DST 4096 (2^47); KZRange PFX 4096 (2^47);
     KZRange nbSeq 1 98047; KZRange (Z.min nbSeq 8) 1 8; KZRange bc 0 91; KZRange LBE 4096 (2^47);
     KZWr FRB 568; KZWr FF 256; KZDisj FF 256 FRB 568]
    [(FRB, 568); (FF, 256)]
    [(FRB, 568); (FF, 256)].
  all: try (lazymatch goal with |- sc_resid _ _ _ (SCDisj _ _ _ _) => kx_side_pre; try sql_oranges; try sql_bvr; try revert C'; try revert RGB; try revert RGA1; try revert RGA2; try revert RGA8; try revert RGC1; try revert RGC2; sql_clear_nonkx; intros; lia end).
  all: try sql_aclose.
  all: kx_mem.
  all: (unfold held in TRANS, CONT, HBC, BOK, HS1, HS2, HS3, S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, S12, S13, S14, S15, S16, S18, S19, S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35, S36, S37, S38, S39, S40, S41, S42, S43, S44, S45, S46, S47, S48, S49, S50, S51, S52, S53, S54, S55, S56, S57, S58, S59, S60, S61, S62, S63, S64, S65, S66, S67, S68, S69, S70, S71, OKLL, OKOF, OKML, OKLL, OKOF, OKML; repeat match goal with HD_ : _ \/ _ |- _ => hold HD_ end; try unfold held in RGB).
  all: try (lazymatch goal with |- evtF _ _ _ _ => fail | |- _ => kx_z end).
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8a6b0) _ _ _ _) => idtac | |- ?G => fail 99 "unexpected goal after the run" G end.
  (* [comment removed for export] *)
  cells_at 1%nat FR. destruct (sql_cb24_words _ FRB _ _ _ FR) as (w8 & w16 & w24 & FR0). clear FR. cbn [app] in FR0.
  cells_at 5%nat FR0. destruct (sql_cb16_words _ FRB _ _ _ FR0) as (w40 & w48 & FR1). clear FR0. cbn [app] in FR1.
  cells_at 12%nat FR1. destruct (sql_cb8_word _ FRB _ _ _ FR1) as (w96 & FR2). clear FR1. cbn [app] in FR2.
  cells_at 14%nat FR2. destruct (sql_cb8_word _ FRB _ _ _ FR2) as (w112 & FR3). clear FR2. cbn [app] in FR3.
  cells_at 26%nat FR3. destruct (sql_cb16_words _ FRB _ _ _ FR3) as (w208 & w216 & FR4). clear FR3. cbn [app] in FR4.
  cells_at 39%nat FR4. destruct (sql_cb8_word _ FRB _ _ _ FR4) as (w312 & FR5). clear FR4. cbn [app] in FR5.
  cells_at 41%nat FR5. destruct (sql_ring_words _ FRB _ _ _ FR5) as (rl & rm & ro & FR10). clear FR5. cbn [app] in FR10.
  eapply (CONT _ w8 w96 w16 w24 w40 p1 w48 (Z_to_bv 64 0) w112 (Z_to_bv 64 0) w208 w216 (Z_to_bv 64 0) (Z_to_bv 64 0) w312 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LITP DST _ 0).
  9: reflexivity. 4: (clear; lia).
  - eapply sql_iinv_linv; eapply sql_iinv_eq2;
      [ eapply TRANS; [exact MUL | exact WMl | exact KXMI | exact FR10 | exact FRF]
      | cbn [sql_frame l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; sql_cells_eq
      | cbn [sql_ffr l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1]; reflexivity ].
  - unfold sql_lfacts; cbn [l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1].
    unfold held in S4; unfold held in S70.
    split; [clear - S4; lia|]. split; [clear - S70; lia|]. split; [exact HS1|]. split; [exact HS2|]. split; [exact HS3|].
    split; [clear - HBC; lia | exact BOK].
  - clear - RG9; first [lia | rewrite ?Z.mod_small by lia; lia].
  - clear - RG9 RG10; lia.
  - clear; lia.
  - clear - RG10; first [lia | rewrite ?Z.mod_small by lia; lia].
  - intros j Hj; exfalso; clear - Hj; lia.
Qed.

End CANSEC1.
