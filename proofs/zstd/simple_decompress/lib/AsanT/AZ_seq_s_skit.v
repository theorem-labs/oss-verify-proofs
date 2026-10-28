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
     AZ_libc_iface AZ_seq_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit AZ_seq_s_lkit2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition sqs_fr29 (P : ssq) (OEND : Z) (c0 c8 c152 c160 c168 c200 c208 c216 : word) : list cell :=
  [CB 16 (v_j0 P); C8 c0; C8 (Z_to_bv 64 (v_DCTX P + 26692)); C8 (Z_to_bv 64 (v_DCTX P + 26688)); C8 (Z_to_bv 64 (v_DCTX P + 26684));
   C8 (Z_to_bv 64 (2147450880 + v_D8 P + 3336)); C8 (Z_to_bv 64 (2147450880 + v_D8 P + 3336)); C8 (Z_to_bv 64 (2147450880 + v_D8 P + 3335));
   C8 (Z_to_bv 64 (v_DCTX P)); C8 (Z_to_bv 64 (v_DST P)); C8 (Z_to_bv 64 OEND); C8 c152; C8 (Z_to_bv 64 (-20));
   C8 (v_dend P); C8 (Z_to_bv 64 (v_PFX P)); C8 (Z_to_bv 64 (v_FF P + 120)); C8 (Z_to_bv 64 (v_FF P)); C8 (Z_to_bv 64 (v_FF P));
   C8 (Z_to_bv 64 139648); C8 (Z_to_bv 64 (v_DCTX P + 29896)); C8 (Z_to_bv 64 (v_PFX P)); C8 c168; C8 c160; C8 c200; C8 c8;
   C8 c208; C8 c216;
   CB 16 (v_j224 P); C8 (Z_to_bv 64 (v_FF P))].

Lemma sqs_frame_app : forall P OEND c0 c8 c152 c160 c168 c200 c208 c216 LP jseq,
  sqs_frame P OEND c0 c8 c152 c160 c168 c200 c208 c216 LP jseq = sqs_fr29 P OEND c0 c8 c152 c160 c168 c200 c208 c216 ++ [C8 (Z_to_bv 64 LP); CB 24 jseq].
Proof. intros. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1]. reflexivity. Qed.

Lemma sqs_fr29_size : forall P OEND c0 c8 c152 c160 c168 c200 c208 c216, length (v_j224 P) = 16%nat ->
  Z.of_nat (cells_size (sqs_fr29 P OEND c0 c8 c152 c160 c168 c200 c208 c216)) = 248.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sqs_fr26_seq : forall (m : amem) P OEND c0 c8 c152 c160 c168 c200 c208 c216 LP a b c,
  rw_cells bsegs m (v_FRB P) (sqs_fr29 P OEND c0 c8 c152 c160 c168 c200 c208 c216 ++ [C8 (Z_to_bv 64 LP); C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 c)]) ->
  length (v_j224 P) = 16%nat ->
  rw_cells bsegs m (v_FRB P + 248) [C8 (Z_to_bv 64 LP)] /\
  rw_cells bsegs m (v_FRB P + 256) [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 c)] /\
  rw_cells bsegs m (v_FRB P) (sqs_fr29 P OEND c0 c8 c152 c160 c168 c200 c208 c216) /\
  rw_cells bsegs m (v_FRB P) (sqs_frame P OEND c0 c8 c152 c160 c168 c200 c208 c216 LP (le8 (Z_to_bv 64 a) ++ le8 (Z_to_bv 64 b) ++ le8 (Z_to_bv 64 c))).
Proof.
  intros m P OEND c0 c8 c152 c160 c168 c200 c208 c216 LP a b c FR L16.
  pose proof FR as FR0. apply rw_cells_app in FR. destruct FR as (F22 & REST). rewrite (sqs_fr29_size _ _ _ _ _ _ _ _ _ _ L16) in REST.
  pose proof REST as REST0.
  change (rw_cells bsegs m (v_FRB P + 248) ([C8 (Z_to_bv 64 LP)] ++ [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 c)])) in REST.
  apply rw_cells_app in REST. destruct REST as (LPC & SQC). cbn [cells_size csize Nat.add] in SQC.
  replace (v_FRB P + 248 + Z.of_nat 8) with (v_FRB P + 256) in SQC by lia.
  split; [exact LPC|]. split; [exact SQC|]. split; [exact F22|].
  rewrite sqs_frame_app. eapply rw_cells_recell; [exact FR0 | |].
  - rewrite !cells_wf_app. destruct FR0 as [(WF & _) _]. rewrite cells_wf_app in WF. destruct WF as [WF _]. split; [exact WF|]. cbn. repeat split.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sqs_fr29_join : forall (m : amem) P OEND c0 c8 c152 c160 c168 c200 c208 c216 LP a b c,
  rw_cells bsegs m (v_FRB P) (sqs_fr29 P OEND c0 c8 c152 c160 c168 c200 c208 c216) ->
  length (v_j224 P) = 16%nat ->
  rw_cells bsegs m (v_FRB P + 248) [C8 (Z_to_bv 64 LP)] ->
  rw_cells bsegs m (v_FRB P + 256) [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 c)] ->
  rw_cells bsegs m (v_FRB P) (sqs_frame P OEND c0 c8 c152 c160 c168 c200 c208 c216 LP (le8 (Z_to_bv 64 a) ++ le8 (Z_to_bv 64 b) ++ le8 (Z_to_bv 64 c))).
Proof.
  intros m P OEND c0 c8 c152 c160 c168 c200 c208 c216 LP a b c F22 L16 LPC SQC.
  assert (REST : rw_cells bsegs m (v_FRB P + 248) ([C8 (Z_to_bv 64 LP)] ++ [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 c)])).
  { apply rw_cells_app. split; [exact LPC|]. cbn [cells_size csize Nat.add]. replace (v_FRB P + 248 + Z.of_nat 8) with (v_FRB P + 256) by lia. exact SQC. }
  assert (FR : rw_cells bsegs m (v_FRB P) (sqs_fr29 P OEND c0 c8 c152 c160 c168 c200 c208 c216 ++ [C8 (Z_to_bv 64 LP); C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 c)])).
  { apply rw_cells_app. split; [exact F22|]. rewrite (sqs_fr29_size _ _ _ _ _ _ _ _ _ _ L16). exact REST. }
  exact (proj2 (proj2 (proj2 (sqs_fr26_seq m P OEND c0 c8 c152 c160 c168 c200 c208 c216 LP a b c FR L16)))).
Qed.

(* [comment removed for export] *)
Definition sqs_slow_post (P : ssq) (OEND LLO LEND LOCV : Z) (c0 c8 c152 c160 c168 c200 c208 c216 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP OP llv mlv : Z)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) : machine_state -> Prop :=
  fun ms' => exists (m2 : amem) (r lp' : Z),
    (exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
       ms' = MS (mkR ra (Z_to_bv 64 (v_FRB P)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m2 (seg_rom bsegs)) /\
    sqs_linv P OEND LLO LEND LOCV m2 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 lp' /\
    0 <= r < 2^64 /\
    (zd_is_error r = true \/ (r = llv + mlv /\ OP + r <= OEND /\ lp' = LP + llv /\ LP + llv <= LEND)).

Lemma sqs_slow_spec : forall P OEND LLO LEND LOCV K m0 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP llv mlv ofs
    ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc,
  sqs_static P OEND LLO LEND LOCV -> 1 <= K <= v_nbSeq P ->
  sqs_linv P OEND LLO LEND LOCV m0 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  rw_cells bsegs m0 (v_FRB P + 256) [C8 (Z_to_bv 64 llv); C8 (Z_to_bv 64 mlv); C8 (Z_to_bv 64 ofs)] ->
  sqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 -> 0 <= llv < 2^18 -> 0 <= mlv < 2^18 ->
  evtF bsegs (v_RNG P) (sqs_slow_post P OEND LLO LEND LOCV c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP llv mlv ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc)
    (MS (mkR ra (Z_to_bv 64 (v_FRB P)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OP) (Z_to_bv 64 OEND) (Z_to_bv 64 (v_FRB P + 256)) (Z_to_bv 64 (v_FRB P + 248))
               (Z_to_bv 64 LEND) (Z_to_bv 64 (v_PFX P)) (Z_to_bv 64 (v_PFX P)) (v_dend P) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x950d4) fc None m0 (seg_rom bsegs)).
Proof.
  intros P OEND LLO LEND LOCV K m0 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP llv mlv ofs ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
         ST HK INV SQC LF HO HL HM.
  pose proof (sqs_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  pose proof (sqs_asan_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as AS.
  pose proof (sqs_copy_asan _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (ART & AST & AREG).
  pose proof (sqs_linv_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as STEP.
  pose proof INV as ((jpad & jseq & FR & FRF) & TLL & TOF & TML & SQB & LIT & XLIT & H5 & XI).
  destruct (sqs_fr_wf _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR) as (L16 & LJ).
  (* [comment removed for export] *)
  rewrite sqs_frame_app in FR. apply rw_cells_app in FR. destruct FR as (F22 & REST). rewrite (sqs_fr29_size _ _ _ _ _ _ _ _ _ _ L16) in REST.
  change (rw_cells bsegs m0 (v_FRB P + 248) ([C8 (Z_to_bv 64 LP)] ++ [CB 24 jseq])) in REST. apply rw_cells_app in REST. destruct REST as (LPC & _).
  destruct LF as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
  destruct P as [ra' gp' tp' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' F' fc' m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB ma FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqs_ffr sqs_xinv sqs_asan sqs_astat v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws v_AI v_fflag v_L v_RNG v_st v_LB v_m0 v_FRB v_FF v_SHF v_D8 v_j0 v_j224 v_jfh v_j144 v_jsh0 v_jsh1] in *.
  sd_static_open ST. unfold held in *.
  destruct XI as (_ & _ & BUF & STK & _).
  destruct AS as (ARD & AHD & _ & _ & ACL & AOUT & ARL & AHL & AZS & _).
  destruct S61 as (ASTK & _).
  unfold zd_execend_stmtA in S66.
  assert (RGS : 4096 <= B0 /\ B1 < 2^47 /\ B0 <= PFX <= OP /\ OP <= OEND <= B1 /\ 4096 <= LP <= LEND /\ LEND + 32 < 2^47 /\
                4096 <= FRB + 256 /\ FRB + 256 + 24 < 2^47 /\ 4096 <= FRB + 248 /\ FRB + 248 + 8 < 2^47 /\ lo <= FRB - 2464 /\ 0 <= FRB < 2^47 /\
                0 <= llv < 2^32 /\ 0 <= mlv < 2^32).
  { clear - S1 S2 S3 S4 S5 S6 S7 S9 S11 S17 S18 S47 L1 L2 HL HM. lia. }
  destruct RGS as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14).
  (* [comment removed for export] *)
  assert (RSQ : rng RNG (FRB + 256) 24) by (destruct ASTK as (_ & R & _); eapply rng_sub; [exact R | clear - S18 S47; lia | clear - S18 S47; lia]).
  assert (RLP : rng RNG (FRB + 248) 8) by (destruct ASTK as (_ & R & _); eapply rng_sub; [exact R | clear - S18 S47; lia | clear - S18 S47; lia]).
  assert (AOSQ : aro RNG m0 (FRB + 256) 24) by (eapply azstk_aro; [exact AZS | clear - S18 S47; lia | clear; lia | clear - S47; lia | exact RSQ]).
  assert (AOLP : aro RNG m0 (FRB + 248) 8) by (eapply azstk_aro; [exact AZS | clear - S18 S47; lia | clear; lia | clear - S47; lia | exact RLP]).
  destruct (AOUT S68) as (ARB & AHB).
  assert (AWIN : areg RNG m0 LP (LEND + 32 - LP) /\ ahull RNG m0 LP (LEND + 32 - LP)).
  { unfold WILDCOPY_OVERLENGTH, DCTX_SIZEOF in *. destruct S67 as [(ELLO & ELEND)|(ELLO & ELEND)]; subst LLO LEND.
    - split; [eapply areg_sub; [exact ARL | clear - L2; lia | clear - L2; lia | clear - L2; lia] | eapply ahull_sub; [exact AHL | clear - L2; lia | clear - L2; lia]].
    - split; [eapply areg_sub; [exact ARD | clear - L2; lia | clear - L2; lia | clear - L2; lia] | eapply ahull_sub; [exact AHD | clear - L2; lia | clear - L2; lia]]. }
  destruct AWIN as (ARL' & AHL').
  eapply evtF_mono.
  - eapply (S66 RNG ra gp tp t0 t1 t2 s0 s1 _ _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 FRB lo OP OEND (FRB + 256) (FRB + 248) LP LEND llv mlv ofs PFX (bv_unsigned dend) B0 B1);
      [ exact BUF | exact G1 | exact G2 | exact G3 | exact G4 | exact SQC | exact LPC | exact G13 | exact G14 | exact HO | exact G5
      | unfold WILDCOPY_OVERLENGTH; exact G6
      | unfold WILDCOPY_OVERLENGTH; eapply rdbl_sub; [exact LIT | clear - L2; lia | clear; lia]
      | unfold apart, WILDCOPY_OVERLENGTH; clear - S12 L2; lia
      | exact G7 | exact G8 | exact G9 | exact G10
      | unfold apart; clear - S24 S18 S47; lia | unfold apart; clear - S24 S18 S47; lia | unfold apart; clear; lia
      | unfold apart, WILDCOPY_OVERLENGTH; clear - S26 S18 S47 L2; lia
      | exact STK | exact G11 | exact G12
      | unfold off_stack; clear - S24 S18 S47; lia | unfold off_stack; clear; lia | unfold off_stack; clear; lia
      | unfold off_stack, WILDCOPY_OVERLENGTH; clear - S26 S18 S47 L2; lia
      | exact S68 | unfold sclr; clear - S53 S18 S47; lia | unfold sclr; clear - S53 S18 S47; lia     (* [comment removed for export] *)
      | unfold AIMG_HI; clear - S53 S18 S47; lia     (* [comment removed for export] *)
      | clear - S48; Z.div_mod_to_equations; lia | clear - S48; Z.div_mod_to_equations; lia     (* [comment removed for export] *)
      | exact ARB | exact AHB | unfold WILDCOPY_OVERLENGTH; exact ARL' | unfold WILDCOPY_OVERLENGTH; exact AHL'
      | exact AOSQ | exact AOLP | exact ART
      | eapply astk_sub; [exact ASTK | clear - S18 S47; lia]
      | exact ACL | exact MI
      | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | symmetry; apply Z_to_bv_bv_unsigned ].
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & lp' & -> & MU & WM & MI' & STK' & BUF' & SQC' & LPC' & HR & RES).
    exists m', r, lp'. split; [do 14 eexists; reflexivity|]. split; [| split; [exact HR | exact RES]].
    assert (MU4 : munch [(OP, OEND); (FRB - 2464, FRB); (FRB, FRB + 280); (FF, FF + 256)] m0 m').
    { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]. intros x Hx. clear - Hx. lia. }
    eapply (STEP m' c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 lp' jpad (le8 (Z_to_bv 64 llv) ++ le8 (Z_to_bv 64 mlv) ++ le8 (Z_to_bv 64 ofs)) OP OEND 2464);
      [ clear; lia | exact MU4 | exact WM | exact MI' | exact BUF' | exact STK' | clear - L1; lia | clear; lia | | ].
    + apply (sqs_fr29_join m' (mkSSQ ra' gp' tp' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' F' fc' m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB ma FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) OEND c0 c8 c152 c160 c168 c200 c208 c216 lp' llv mlv ofs); [ | exact L16 | exact LPC' | exact SQC'].
      eapply rw_cells_transport; [exact F22 | exact MU | exact WM |].
      rewrite (sqs_fr29_size (mkSSQ ra' gp' tp' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' F' fc' m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB ma FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) OEND c0 c8 c152 c160 c168 c200 c208 c216 L16). cbn [disjoint_from v_FRB]. split; [clear - S24 S18 S47 G3 G4; lia|]. split; [clear; lia|]. split; [clear; lia| exact I].
    + eapply rw_cells_transport; [exact FRF | exact MU | exact WM |].
      cbn [disjoint_from cells_size csize Nat.add]. split; [clear - S55 G3 G4; lia|]. split; [clear - S50 S18 S47; lia|]. split; [clear - S50 S18 S47; lia| exact I].
Qed.

End CANSEC1.
