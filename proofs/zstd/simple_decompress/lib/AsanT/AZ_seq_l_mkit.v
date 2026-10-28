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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_hkit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma sql_dctx_rng : forall P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP,
  sql_static P OEND LLO LEND LOCV -> sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  rng (l_RNG P) (l_DCTX P) DCTX_SIZEOF /\ rng (l_RNG P) (l_DCTX P + 30096) 276.
Proof.
  intros P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV.
  pose proof (sql_asan_now P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV) as AS.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  cbn [sql_asan l_RNG l_DCTX] in *.
  destruct AS as (AD & _). destruct (AD ltac:(unfold DCTX_SIZEOF; clear; lia)) as (_ & _ & R1 & _).
  split; [exact R1|]. eapply rng_sub'; [exact R1 | unfold DCTX_SIZEOF; clear; lia].
Qed.

(* [comment removed for export] *)
Lemma sql_linv_switch : forall P OEND LLO LEND m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP,
  sql_static P OEND LLO LEND 2 -> sql_linv P OEND LLO LEND 2 m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  forall m2 c8' c16' c24' c32' c88' c96' c120' c128' c160' c224' c232' c248' c264' c304' c312' c320' c328' c336' c352' c368' c376' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' rl' rm' ro' LP' jpad jseq,
  munch [(l_DCTX P + 30368, l_DCTX P + 30368 + 4); (l_FRB P, l_FRB P + 568); (l_FF P, l_FF P + 256)] m1 m2 -> wmono bsegs m1 m2 -> mem_inv bsegs m2 ->
  rw_cells bsegs m2 (l_FRB P) (sql_frame P OEND c8' c16' c24' c32' c88' c96' c120' c128' c160' c224' c232' c248' c264' c304' c312' c320' c328' c336' c352' c368' c376' rl' rm' ro' LP' jseq) ->
  rw_cells bsegs m2 (l_FF P) (sql_ffr P cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' jpad) ->
  rw_cells bsegs m2 (l_DCTX P + 30096) (h5_vcells (l_ws P) (Z_to_bv 64 0)) ->
  sql_linv P OEND (l_DCTX P + 30372) (l_DCTX P + 95908) 0 m2 c8' c16' c24' c32' c88' c96' c120' c128' c160' c224' c232' c248' c264' c304' c312' c320' c328' c336' c352' c368' c376' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' rl' rm' ro' LP'.
Proof.
  intros P OEND LLO LEND m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV m2 c8' c16' c24' c32' c88' c96' c120' c128' c160' c224' c232' c248' c264' c304' c312' c320' c328' c336' c352' c368' c376' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' rl' rm' ro' LP' jpad jseq MUL WML MI2 FR FRF H5V2.
  destruct INV as (_ & TLL & TOF & TML & SQB & LIT & XLIT & (H5V & H5L) & XI).
  split; [exists jpad, jseq; split; [exact FR | exact FRF]|]. clear FR FRF.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  cbn [sql_xinv l_FRB l_FF l_LLT l_OFT l_MLT l_SEQ l_sq l_tLL l_tOF l_tML l_DCTX l_ws l_m] in *.
  sd_static_open ST. unfold held in *.
  pose proof (tbl_len_LL _ OKLL) as LLL. pose proof (tbl_len_OF _ OKOF) as LOF. pose proof (tbl_len_ML _ OKML) as LML.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & SAV & GAP & SHS & MU & WM & MI1).
  (* [comment removed for export] *)
  assert (BDL : (6443008 <= DCTX /\ DCTX + 95992 <= 2147446784) \/ (17594333495296 <= DCTX /\ DCTX + 95992 <= ATOP)).
  { cbn [sql_asan] in S62. destruct S62 as (ARD & _). destruct (ARD ltac:(unfold DCTX_SIZEOF; clear; lia)) as (BD & _). pose proof (ablk_lits _ _ BD) as BL. unfold DCTX_SIZEOF in BL. exact BL. }
  unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, h5_vcells in *.
  split; [eapply bytes_at_transport; [exact TLL | exact MUL | cbn [disjoint_from]; split; [clear - S37 LLL; lia | split; [clear - S28 S18 S47 LLL; lia| split; [clear - S58 LLL; lia|exact I]]]]|].
  split; [eapply bytes_at_transport; [exact TOF | exact MUL | cbn [disjoint_from]; split; [clear - S38 LOF; lia | split; [clear - S29 S18 S47 LOF; lia| split; [clear - S59 LOF; lia|exact I]]]]|].
  split; [eapply bytes_at_transport; [exact TML | exact MUL | cbn [disjoint_from]; split; [clear - S39 LML; lia | split; [clear - S30 S18 S47 LML; lia| split; [clear - S60 LML; lia|exact I]]]]|].
  split; [eapply bytes_at_transport; [exact SQB | exact MUL | cbn [disjoint_from]; rewrite length_map; split; [clear - S40; lia | split; [clear - S25 S18 S47; lia| split; [clear - S56; lia|exact I]]]]|].
  assert (XL2 : rdbl bsegs m2 (DCTX + 30372) (DCTX + 95940)).
  { eapply rdbl_transport; [exact (XLIT eq_refl) | exact MUL | intros x Hx; left; cbn [outside]; split; [clear - Hx; lia | split; [clear - S27 S18 S47 Hx; lia| split; [clear - S54 Hx; lia|exact I]]]]. }
  split; [replace (DCTX + 95908 + 32) with (DCTX + 95940) by lia; exact XL2|].
  split; [intros _; exact XL2|].
  split; [split; [exact H5V2 | exact H5L]|].
  split; [exists r0', r1', r2'; eapply rw_cells_transport; [exact REP | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear; lia | split; [clear - S27 S18 S47; lia| split; [clear - S54; lia|exact I]]]]|].
  split; [eapply rw_cells_transport; [exact HH3 | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear; lia | split; [clear - S27 S18 S47; lia| split; [clear - S54; lia|exact I]]]]|].
  split; [eapply stk_transport_disjoint; [exact BUF | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - S32; lia | split; [clear - S24 S18 S47; lia| split; [clear - S55; lia|exact I]]]]|].
  split; [eapply stk_transport_disjoint; [exact STK | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - S27 S18 S47; lia | split; [clear; lia| split; [clear - S50 S18 S47; lia|exact I]]]]|].
  split; [eapply rw_cells_transport; [exact SAV | exact MUL | exact WML | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - S27 S18 S47; lia | split; [clear - S47; lia| split; [clear - S50 S18 S47; lia|exact I]]]]|].
  split; [eapply stk_transport_disjoint; [exact GAP | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - S27 S18 S47; lia | split; [clear; lia| split; [clear - S50 S18 S47; lia|exact I]]]]|].
  split; [eapply rw_cells_transport; [exact SHS | exact MUL | exact WML | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - BDL S52 S53; pose proof atop_range; lia | split; [clear - S53 S18 S47; lia| split; [clear - S49 S52 S53; lia|exact I]]]]|].
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MUL]; unfold sub_fp, sql_Wb; cbn [outside]; unfold DCTX_litBufferLocation; intros x Hx; clear - Hx S47; lia]|].
  split; [eapply wmono_trans; [exact WM | exact WML] | exact MI2].
Qed.

End CANSEC1.
