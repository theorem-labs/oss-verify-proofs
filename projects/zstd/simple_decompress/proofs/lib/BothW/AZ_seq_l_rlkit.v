(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk Frame.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_lkit2.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma sql_ediv8 : forall q r, 0 <= r <= 7 -> (8 * q + r) / 8 = q /\ (8 * q + r) mod 8 = r.
Proof. intros q r H. split; [symmetry; apply (Z.div_unique (8 * q + r) 8 q r); lia | symmetry; apply (Z.mod_unique (8 * q + r) 8 q r); lia]. Qed.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition sql_ffr_rest (P : slq) (sLL sOF sML : Z) (p0 p1 p2 : word) : list cell :=
  [C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (l_LLT P + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (l_OFT P + 8)); C8 (Z_to_bv 64 sML); C8 (Z_to_bv 64 (l_MLT P + 8));
   C8 p0; C8 p1; C8 p2; CB 104 (l_j144 P); C8 (Z_to_bv 64 (l_fflag P (l_L P) 2 (l_FF P)))].
Lemma sql_ffr_app : forall P cw bc ptr sLL sOF sML p0 p1 p2 jpad,
  sql_ffr P cw bc ptr sLL sOF sML p0 p1 p2 jpad = [CB 32 (l_jfh P)] ++ sbd_cells cw bc jpad ptr (l_SEQ P) ++ sql_ffr_rest P sLL sOF sML p0 p1 p2.
Proof. intros. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1]. reflexivity. Qed.

(* [comment removed for export] *)
Definition sql_rl_post (P : slq) (OEND LLO LEND LOCV : Z) (c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) : machine_state -> Prop :=
  fun ms' => exists (m2 : amem) (cw2 : word),
    (exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
       ms' = MS (mkR ra (Z_to_bv 64 (l_FRB P)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m2 (seg_rom bsegs)) /\
    sql_linv P OEND LLO LEND LOCV m2 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw2 (bc mod 8) (ptr - bc / 8) sLL sOF sML p0 p1 p2 rl rm ro LP.

Lemma sql_rl_spec : forall P OEND LLO LEND LOCV m0 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP
    ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc,
  sql_static P OEND LLO LEND LOCV ->
  sql_linv P OEND LLO LEND LOCV m0 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  0 <= bc <= 64 -> l_SEQ P + 8 <= ptr -> ptr <= l_SEQ P + zlen (l_sq P) - 8 ->
  evtF bsegs (l_RNG P) (sql_rl_post P OEND LLO LEND LOCV c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc)
    (MS (mkR ra (Z_to_bv 64 (l_FRB P)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (l_FF P + 32)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x967a8) fc None m0 (seg_rom bsegs)).
Proof.
  intros P OEND LLO LEND LOCV m0 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
         ST INV HBC HP1 HP2.
  pose proof (sql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  pose proof (sql_asan_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as AS.
  pose proof (sql_linv_fsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as UFL.
  pose proof (sql_linv_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as STEP.
  pose proof INV as ((jpad & jseq & FR & FRF) & TLL & TOF & TML & SQB & LIT & XLIT & H5 & XI).
  (* [comment removed for export] *)
  rewrite sql_ffr_app in FRF. apply rw_cells_app in FRF. destruct FRF as (F0 & FRF). apply rw_cells_app in FRF. destruct FRF as (BDC & F2).
  cbn [cells_size csize Nat.add length] in BDC. cbn [cells_size csize Nat.add length sbd_cells] in F2.
  destruct P as [ra' gp' tp' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' F' fc' m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB ma FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  cbn [sql_xinv sql_asan sql_astat sql_pro l_ra l_gp l_tp l_s0 l_s1 l_s2 l_s3 l_s4 l_s5 l_s6 l_s7 l_s8 l_s9 l_s10 l_s11 l_F l_fc l_m l_SPV l_lo l_DCTX l_DST l_CAP l_B0 l_B1 l_SEQ l_nbSeq l_LLT l_MLT l_OFT l_PFX l_LITP l_LBE l_LITB l_LOC l_sq l_tLL l_tOF l_tML l_huf l_r0 l_r1 l_r2 l_pde l_dend l_expd l_pcs l_dsz l_bt l_stg l_le l_fe l_ws l_AI l_fflag l_L l_RNG l_st l_LB l_m0 l_FRB l_FF l_SHF l_D8 l_j0 l_j384 l_jfh l_j144 l_jsh0 l_jsh1] in *.
  sd_static_open ST. unfold held in *.
  destruct XI as (_ & _ & BUF & STK & _).
  destruct AS as (_ & _ & ARS & _ & _ & _ & _ & _ & AZS & ART).
  destruct S61 as (ASTK & _ & _ & _ & _ & _ & _ & _ & _ & _ & ESHF & RFF & RSHF & _).
  destruct S63 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ABFF).
  unfold zd_reload_int_stmtA in S72.
  assert (LSQ : Z.of_nat (length (map (Z_to_bv 8) sq)) = zlen sq) by (rewrite length_map; reflexivity).
  assert (RGS : 4096 <= FF + 32 /\ FF + 32 + 40 < 2^47 /\ 4096 <= SEQ /\ SEQ + zlen sq < 2^47 /\ (FF + 32) mod 8 = 0 /\
                (FF + 32 + 40 <= SEQ \/ SEQ + zlen sq <= FF + 32) /\ lo <= FRB - 16 /\ FRB < 2^47 /\
                (FF + 32 + 40 <= lo \/ FRB <= FF + 32) /\ (SEQ + zlen sq <= lo \/ FRB <= SEQ) /\ 0 <= FRB - 16).
  { clear - S13 S14 S15 S17 S18 S47 S49 S50 S51 S56 S25. Z.div_mod_to_equations. lia. }
  destruct RGS as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  (* [comment removed for export] *)
  assert (ABD : app_blk (FF + 32) (FF + 32 + 40)).
  { eapply app_blk_sub; [apply ablk_app_blk; [exact ABFF | clear; lia] | clear; lia | clear; lia | clear; lia]. }
  assert (AOBD : aro RNG m0 (FF + 32) 40).
  { split; [eapply unpoisoned_sub; [exact UFL | clear; lia | clear; lia]|].
    split; [eapply rng_sub; [exact RFF | clear; lia | clear; lia]|].
    eapply rng_sub; [exact RSHF | |]; rewrite ESHF; unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - S51; Z.div_mod_to_equations; lia. }
  assert (AOSQ : aro RNG m0 SEQ (Z.of_nat (length (map (Z_to_bv 8) sq)))).
  { rewrite LSQ. apply aregU_aro. apply ARS. clear - S15; lia. }
  eapply evtF_mono.
  - eapply (S72 RNG ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 FRB lo (FF + 32) SEQ bc ptr cw jpad (map (Z_to_bv 8) sq));
      [ exact BDC | exact SQB | exact G1 | exact G2 | exact G3 | rewrite LSQ; exact G4 | exact G5 | rewrite LSQ; exact G6
      | exact HBC | exact HP1 | rewrite LSQ; exact HP2
      | exact STK | exact G7 | exact G8 | exact G9 | rewrite LSQ; exact G10
      | exact ABD | exact AOBD | exact AOSQ | exact ART
      | eapply astk_sub; [exact ASTK | clear - S18 S47; lia]
      | exact MI ].
  - intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & cw' & -> & MU & WM & MI' & STK' & BDC').
    exists m', cw'. split; [do 15 eexists; reflexivity|].
    assert (MU4 : munch [(DST, DST); (FRB - 16, FRB); (FRB, FRB + 632); (FF, FF + 256)] m0 m').
    { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]. intros x Hx. clear - Hx. lia. }
    eapply (STEP m' c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw' (bc mod 8) (ptr - bc / 8) sLL sOF sML p0 p1 p2 rl rm ro LP jpad jseq DST DST 16);
      [ clear; lia | exact MU4 | exact WM | exact MI' | | exact STK' | clear; lia | clear - S4; lia | | ].
    + (* [comment removed for export] *)
      eapply stk_transport_disjoint; [exact BUF | exact MU | exact WM |].
      cbn [disjoint_from]. split; [clear - S55 S68; lia|]. split; [clear - S24 S18 S47 S68; lia| exact I].
    + eapply rw_cells_transport; [exact FR | exact MU | exact WM |].
      cbn [disjoint_from sql_frame cells_size csize Nat.add l_FRB].
      split; [clear - S50 S18 S47; lia|]. split; [clear; lia| exact I].
    + rewrite sql_ffr_app. cbn [l_jfh l_SEQ sql_ffr_rest l_LLT l_OFT l_MLT l_j144 l_fflag l_L l_FF]. apply rw_cells_app. split.
      * eapply rw_cells_transport; [exact F0 | exact MU | exact WM |]. cbn [disjoint_from cells_size csize Nat.add length]. split; [clear; lia|]. split; [clear - S50 S18 S47; lia| exact I].
      * apply rw_cells_app. cbn [cells_size csize Nat.add length]. split; [exact BDC'|].
        eapply rw_cells_transport; [exact F2 | exact MU | exact WM |].
        cbn [disjoint_from cells_size csize Nat.add length sbd_cells sql_ffr_rest].
        split; [clear; lia|]. split; [clear - S50 S18 S47; lia| exact I].
Qed.

End CANSEC1.
