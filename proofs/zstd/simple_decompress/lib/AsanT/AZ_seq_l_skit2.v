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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_lkit2 AZ_seq_l_skit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

Lemma sql_slow2_spec : forall P OEND LLO LEND LOCV K m0 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP llv mlv ofs ow
    ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 (F : bvmap 5 word) fc,
  sql_static P OEND LLO LEND LOCV -> 1 <= K <= l_nbSeq P ->
  sql_linv P OEND LLO LEND LOCV m0 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  rw_cells bsegs m0 (l_FRB P + 544) [C8 (Z_to_bv 64 llv); C8 (Z_to_bv 64 mlv); C8 (Z_to_bv 64 ofs)] ->
  sql_lfacts P OEND LLO LEND (100 + 100 * (l_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 -> 0 <= llv < 2^18 -> 0 <= mlv < 2^18 ->
  ow = LP + llv - 32 -> LP + llv <= LEND -> LEND + 32 <= OEND ->
  evtF bsegs (l_RNG P) (sql_slow_post P OEND LLO LEND LOCV c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP llv mlv ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc)
    (MS (mkR ra (Z_to_bv 64 (l_FRB P)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OP) (Z_to_bv 64 OEND) (Z_to_bv 64 ow) (Z_to_bv 64 (l_FRB P + 544)) (Z_to_bv 64 (l_FRB P + 536))
               (Z_to_bv 64 LEND) (Z_to_bv 64 (l_PFX P)) (Z_to_bv 64 (l_PFX P)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (l_dend P) t4 t5 t6)
        F (Z_to_bv 64 0x95d74) fc None m0 (seg_rom bsegs)).
Proof.
  intros P OEND LLO LEND LOCV K m0 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP llv mlv ofs ow ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 F fc
         ST HK INV SQC LF HO HL HM HOW HLE HL32.
  pose proof (sql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  pose proof (sql_asan_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as AS.
  pose proof (sql_copy_asan _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (ART & AST & AREG).
  pose proof (sql_linv_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as STEP.
  pose proof INV as ((jpad & jseq & FR & FRF) & TLL & TOF & TML & SQB & LIT & XLIT & H5 & XI).
  destruct (sql_fr_wf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as (L0 & L320 & LJ). pose proof (conj L0 L320) as L16.
  (* [comment removed for export] *)
  rewrite sql_frame_app in FR. apply rw_cells_app in FR. destruct FR as (F22 & REST). rewrite (sql_fr22_size _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L16) in REST.
  change (rw_cells bsegs m0 (l_FRB P + 536) ([C8 (Z_to_bv 64 LP)] ++ [CB 24 jseq])) in REST. apply rw_cells_app in REST. destruct REST as (LPC & _).
  destruct LF as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
  destruct P as [ra' gp' tp' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' F' fc' m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB ma FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  cbn [sql_ffr sql_xinv sql_asan sql_astat l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in *.
  sd_static_open ST. unfold held in *.
  destruct XI as (_ & _ & BUF & STK & _).
  destruct AS as (ARD & AHD & _ & _ & ACL & AOUT & ARL & AHL & AZS & _).
  destruct S61 as (ASTK & _).
  unfold zd_execend_split_stmtA in S65.
  assert (RGS : 4096 <= B0 /\ B1 < 2^47 /\ B0 <= PFX <= OP /\ OP <= OEND <= B1 /\ 4096 <= LP <= LEND /\ LEND + 32 < 2^47 /\
                4096 <= FRB + 544 /\ FRB + 544 + 24 < 2^47 /\ 4096 <= FRB + 536 /\ FRB + 536 + 8 < 2^47 /\ lo <= FRB - 2480 /\ 0 <= FRB < 2^47 /\
                0 <= llv < 2^32 /\ 0 <= mlv < 2^32).
  { clear - S1 S2 S3 S4 S5 S6 S7 S9 S11 S17 S18 S47 L1 L2 HL HM. lia. }
  destruct RGS as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14).
  (* [comment removed for export] *)
  assert (RSQ : rng RNG (FRB + 544) 24) by (destruct ASTK as (_ & R & _); eapply rng_sub; [exact R | clear - S18 S47; lia | clear - S18 S47; lia]).
  assert (RLP : rng RNG (FRB + 536) 8) by (destruct ASTK as (_ & R & _); eapply rng_sub; [exact R | clear - S18 S47; lia | clear - S18 S47; lia]).
  assert (AOSQ : aro RNG m0 (FRB + 544) 24) by (eapply azstk_aro; [exact AZS | clear - S18 S47; lia | clear; lia | clear - S47; lia | exact RSQ]).
  assert (AOLP : aro RNG m0 (FRB + 536) 8) by (eapply azstk_aro; [exact AZS | clear - S18 S47; lia | clear; lia | clear - S47; lia | exact RLP]).
  destruct (AOUT S68) as (ARB & AHB).
  assert (AWIN : areg RNG m0 LP (LEND - LP) /\ ahull RNG m0 LP (LEND - LP)).
  { unfold WILDCOPY_OVERLENGTH, DCTX_SIZEOF in *. destruct S67 as [(ELLO & ELEND)|(ELLO & ELEND)]; subst LLO LEND.
    - split; [eapply areg_sub; [exact ARL | clear - L2; lia | clear - L2; lia | clear - L2; lia] | eapply ahull_sub; [exact AHL | clear - L2; lia | clear - L2; lia]].
    - split; [eapply areg_sub; [exact ARD | clear - L2; lia | clear - L2; lia | clear - L2; lia] | eapply ahull_sub; [exact AHD | clear - L2; lia | clear - L2; lia]]. }
  destruct AWIN as (ARL' & AHL').
  eapply evtF_mono.
  - eapply (S65 RNG ra gp tp t0 t1 t2 s0 s1 _ _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ t4 t5 t6 F fc m0 FRB lo OP OEND ow (FRB + 544) (FRB + 536) LP LEND llv mlv ofs PFX (bv_unsigned dend) B0 B1);
      [ exact BUF | exact G1 | exact G2 | exact G3 | exact G4 | clear - HOW G5 HL; lia | clear - HOW HLE HL32; lia | exact SQC | exact LPC | exact G13 | exact G14 | exact HO | exact G5
      | clear - G6; lia
      | eapply rdbl_sub; [exact LIT | clear - L2; lia | clear; lia]
      | unfold apart; clear - S12 L2; lia
      | exact G7 | exact G8 | exact G9 | exact G10
      | unfold apart; clear - S24 S18 S47; lia | unfold apart; clear - S24 S18 S47; lia | unfold apart; clear; lia
      | unfold apart; clear - S26 S18 S47 L2; lia
      | exact STK | exact G11 | exact G12
      | unfold off_stack; clear - S24 S18 S47; lia | unfold off_stack; clear; lia | unfold off_stack; clear; lia
      | unfold off_stack; clear - S26 S18 S47 L2; lia
      | exact S68 | unfold sclr; clear - S53 S18 S47; lia | unfold sclr; clear - S53 S18 S47; lia     (* [comment removed for export] *)
      | unfold AIMG_HI; clear - S53 S18 S47; lia     (* [comment removed for export] *)
      | clear - S48; Z.div_mod_to_equations; lia | clear - S48; Z.div_mod_to_equations; lia     (* [comment removed for export] *)
      | exact ARB | exact AHB | exact ARL' | exact AHL'
      | exact AOSQ | exact AOLP | exact ART
      | eapply astk_sub; [exact ASTK | clear - S18 S47; lia]
      | exact ACL | exact MI
      | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | symmetry; apply Z_to_bv_bv_unsigned ].
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & lp' & -> & MU & WM & MI' & STK' & BUF' & SQC' & LPC' & HR & RES).
    exists m', r, lp'. split; [do 14 eexists; reflexivity|]. split; [| split; [exact HR | exact RES]].
    assert (MU4 : munch [(OP, OEND); (FRB - 2480, FRB); (FRB, FRB + 568); (FF, FF + 256)] m0 m').
    { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]. intros x Hx. clear - Hx. lia. }
    eapply (STEP m' c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro lp' jpad (le8 (Z_to_bv 64 llv) ++ le8 (Z_to_bv 64 mlv) ++ le8 (Z_to_bv 64 ofs)) OP OEND 2480);
      [ clear; lia | exact MU4 | exact WM | exact MI' | exact BUF' | exact STK' | clear - L1; lia | clear; lia | | ].
    + apply (sql_fr22_join m' (mkSLQ ra' gp' tp' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' F' fc' m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB ma FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1) OEND c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 rl rm ro lp' llv mlv ofs); [ | exact L16 | exact LPC' | exact SQC'].
      eapply rw_cells_transport; [exact F22 | exact MU | exact WM |].
      rewrite (sql_fr22_size (mkSLQ ra' gp' tp' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' F' fc' m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB ma FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1) OEND c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 rl rm ro L16). cbn [disjoint_from l_FRB]. split; [clear - S24 S18 S47 G3 G4; lia|]. split; [clear; lia|]. split; [clear; lia| exact I].
    + eapply rw_cells_transport; [exact FRF | exact MU | exact WM |].
      cbn [disjoint_from cells_size csize Nat.add]. split; [clear - S55 G3 G4; lia|]. split; [clear - S50 S18 S47; lia|]. split; [clear - S50 S18 S47; lia| exact I].
Qed.

End CANSEC1.
