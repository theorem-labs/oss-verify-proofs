From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib Frame.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCLemmas1 CmpMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCut0 CmpCutSM CmpCutSmA BzCFactsSmA BzCFactsSmB BzCFactsSd BzCNumZ.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.
Local Ltac U.Bz.BzTac.st_eq ::= CmpStEq.st_eq_fast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import UKit U0_cmp_sdBV U0_sd4P U0_sd4Z U0_sd4Y U0_cmp_smF U0_cmp_smV U0_smSpec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import U0_cmp_sdC3 U0_cmp_smQ.

Lemma U0_sm_epi : forall (Q : machine_state -> Prop) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SP : Z)
    (m : word -> option byte) (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 rra : word)
    (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  0 <= SP -> SP + 1200 <= 2^64 ->
  rw_cells s0segs m (SP + 1096) [C8 r11; C8 r10; C8 r9; C8 r8; C8 r7; C8 r6; C8 r5; C8 r4; C8 r3; C8 r2; C8 r1; C8 r0; C8 rra] ->
  evt s0segs Q (MS (mkR rra (Z_to_bv 64 (SP + 1200)) gp tp t0 t1 t2 r0 r1 a0 a1 a2 a3 a4 a5 a6 a7 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 t3 t4 t5 t6)
                    F (ret_pc rra) fc None m (seg_rom s0segs)) ->
  evt s0segs Q (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x20298) fc None m (seg_rom s0segs)).
Proof.
  intros Q gp tp F fc SP m r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 rra ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SPL SPH SAV K.
  repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => wstep end).
  enter_with K. st_eq.
Qed.

Lemma rwc_mid : forall segs (m : word -> option byte) A cs (k n : nat) B,
  rw_cells segs m A cs -> A + Z.of_nat (cells_size (firstn k cs)) = B -> rw_cells segs m B (firstn n (skipn k cs)).
Proof.
  intros segs m A cs k n B H HB.
  rewrite <- (firstn_skipn k cs) in H. apply rw_cells_app_iff_c in H. destruct H as [_ H]. rewrite HB in H.
  rewrite <- (firstn_skipn n (skipn k cs)) in H. apply rw_cells_app_iff_c in H. destruct H as [H _]. exact H.
Qed.

Lemma hc_split : forall segs (m : word -> option byte) (P : Z) (H : sdw), rw_cells segs m (P + 888) (sd_hc H) ->
  rw_cells segs m (P + 904) [C8 (h904 H)] /\ rw_cells segs m (P + 928) [C8 (h928 H)] /\ rw_cells segs m (P + 944) [C8 (h944 H)] /\
  rw_cells segs m (P + 960) [C8 (h960 H)] /\ rw_cells segs m (P + 976) [C8 (h976 H); C8 (h984 H)] /\
  rw_cells segs m (P + 992) [C8 (h992 H); C8 (h1000 H); C8 (h1008 H); C8 (h1016 H)] /\
  rw_cells segs m (P + 1024) [C8 (h1024 H)] /\ rw_cells segs m (P + 1032) [C8 (h1032 H)].
Proof.
  intros segs m P H HC.
  refine (conj (rwc_mid segs m _ (sd_hc H) 2 1 _ HC _) (conj (rwc_mid segs m _ (sd_hc H) 5 1 _ HC _)
         (conj (rwc_mid segs m _ (sd_hc H) 7 1 _ HC _) (conj (rwc_mid segs m _ (sd_hc H) 9 1 _ HC _)
         (conj (rwc_mid segs m _ (sd_hc H) 11 2 _ HC _) (conj (rwc_mid segs m _ (sd_hc H) 13 4 _ HC _)
         (conj (rwc_mid segs m _ (sd_hc H) 17 1 _ HC _) (rwc_mid segs m _ (sd_hc H) 18 1 _ HC _))))))));
    cbn [firstn skipn sd_hc cells_size csize Nat.add]; lia.
Qed.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section SMT.
  Hypothesis EMIT : U0_sd_emit_spec.
  Hypothesis POST : sm_post_ok.

  Theorem U0_sendMTF_gen : sendMTF_spec.
  Proof.
    unfold sendMTF_spec.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cx g e lo sv.
    cbv zeta.
    intros A0 GM GBS GZB EM AM CM MI ST LOW CLO AL CX SEP IMG ZI BWOK HNB ROOM SFA SFB SDF.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    pose proof CX as CXL. unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE in CXL. cbv zeta in CXL.
    destruct CXL as (XE0 & XE1 & XA10 & XA11 & XA20 & XA21 & _).
    assert (CEP : CEIL <= bv_unsigned sp - 1200) by lia.
    assert (PHI : bv_unsigned sp - 1200 + 1200 <= 18446744073709551616) by lia.
    assert (PHI2 : bv_unsigned sp - 1200 + 1200 <= 2^64) by (change (2^64) with 18446744073709551616; lia).
    lazymatch goal with |- evt _ ?QQ _ =>
      refine (U0_sm_front ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cx g e lo sv QQ
                A0 GM EM AM CM MI ST LOW CLO AL CX SEP IMG SFA SFB _) end.
    intros m1 J0 Jm J3 Jx J44 Jf w16 w896 w912 w936 w1024
           ra1 t0_1 t1_1 t2_1 s1_1 a0_1 a1_1 a2_1 a3_1 a4_1 a5_1 a6_1 a7_1 s2_1 s3_1 s4_1 s5_1 s6_1 s7_1 s8_1 s10_1 s11_1 t3_1 t4_1 t5_1 t6_1.
    intros EB1 AM1 CM1 MI1 ST1 MU1 WM1 L0 Lm L3 Lx L44 Lf FJ0 C16 FJm C816 FJ3 BLK FJx FJ44 FJf SAV.
    pose proof EB1 as EBx. destruct EBx as (EH1 & INU & UNS & EH2 & MTF & SEL & SLM & LEN & COD & RFQ & LNP).
    pose proof AM1 as AMx. destruct AMx as (AR1 & AR2 & FTB).
    cbn [est_B e_selector e_selectorMtf e_len e_code e_inUse] in SEL, SLM, LEN, COD, INU.
    assert (EH1e : rw_cells s0segs m1 (c_E cx) (EHEAD1 cx g e)).
    { unfold EHEAD1 in EH1 |- *.
      cbn [est_B e_mode e_state e_avail_in_expect e_origPtr e_state_in_ch e_state_in_len e_nblock e_bw e_state_out_pos e_nInUse] in EH1.
      exact EH1. }
    assert (EH2e : rw_cells s0segs m1 (c_E cx + 640) (EHEAD2 cx g e)).
    { unfold EHEAD2 in EH2 |- *.
      cbn [est_B e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF] in EH2.
      exact EH2. }
    assert (AR2' : u8arr s0segs m1 (c_A2 cx) (zb8 (zbl (e_arr2 e) (e_nblock e) (e_bw e)) ARR2_SIZE)) by (rewrite ZI; exact AR2).
    assert (L44' : Z.of_nat (length J44) = 16) by (rewrite L44; reflexivity).
    assert (MIDB : lo <= bv_unsigned sp - 1200 <= bv_unsigned sp) by lia.
    destruct (stk_split s0segs m1 lo (bv_unsigned sp - 1200) (bv_unsigned sp) ST1 MIDB) as [ST1a _].
    assert (LO16 : lo + 16 <= bv_unsigned sp - 1200) by lia.
    assert (C816a : rw_cells s0segs m1 (bv_unsigned sp - 1200 + 816) [C8 (Z_to_bv 64 (c_E cx + 1704))]).
    { refine (rwc_mid s0segs m1 _ [C8 (Z_to_bv 64 (c_E cx + 1704)); C8 (Z_to_bv 64 (18446744073709551615 - (c_E cx + 1704)))] 0 1 _ C816 _).
      cbn [firstn skipn cells_size csize Nat.add]; lia. }
    assert (C816b : rw_cells s0segs m1 (bv_unsigned sp - 1200 + 824) [C8 (Z_to_bv 64 (18446744073709551615 - (c_E cx + 1704)))]).
    { refine (rwc_mid s0segs m1 _ [C8 (Z_to_bv 64 (c_E cx + 1704)); C8 (Z_to_bv 64 (18446744073709551615 - (c_E cx + 1704)))] 1 1 _ C816 _).
      cbn [firstn skipn cells_size csize Nat.add]; lia. }
    assert (V816 : frdW s0segs [(c_E cx + 19706, c_E cx + 37708); (c_E cx + 39256, c_E cx + 45448);
                                (bv_unsigned sp - 1200 + 888, bv_unsigned sp - 1200 + 1040); (bv_unsigned sp - 1200 + 1044, bv_unsigned sp - 1200 + 1060);
                                (bv_unsigned sp - 1200 - 16, bv_unsigned sp - 1200)] m1
                        (bv_unsigned sp - 1200 + 816) [C8 (Z_to_bv 64 (c_E cx + 1704))]).
    { apply frdW_intro; [exact C816a|]. cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia. }
    assert (V824 : frdW s0segs [(c_E cx + 19706, c_E cx + 37708); (c_E cx + 39256, c_E cx + 45448);
                                (bv_unsigned sp - 1200 + 888, bv_unsigned sp - 1200 + 1040); (bv_unsigned sp - 1200 + 1044, bv_unsigned sp - 1200 + 1060);
                                (bv_unsigned sp - 1200 - 16, bv_unsigned sp - 1200)] m1
                        (bv_unsigned sp - 1200 + 824) [C8 (Z_to_bv 64 (18446744073709551615 - (c_E cx + 1704)))]).
    { apply frdW_intro; [exact C816b|]. cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia. }
    assert (BEeq : U0_sd4Z.BE (est_C e znew znew znew znew znew znew) (smA_ng e) (sm_alpha e) (smB_nsel e znew znew znew znew znew) znew
                   = smD_b4 e znew znew znew znew znew znew znew).
    { unfold U0_sd4Z.BE, U0_sd4Z.BD, U0_sd4Z.BC, U0_sd4Z.BC3, U0_sd4Z.BB, U0_sd4Z.BA, U0_sd4Z.IN16,
             smD_b4, smD_b3, smD_b2, smD_b1, smD_b0, smD_in16, est_C.
      cbn [e_len e_selectorMtf e_inUse e_bw].
      reflexivity. }
    assert (NLE : bw_numZ (U0_sd4Z.BE (est_C e znew znew znew znew znew znew) (smA_ng e) (sm_alpha e) (smB_nsel e znew znew znew znew znew) znew)
                  <= bw_numZ (e_bw (est_D e znew znew znew znew znew znew znew))).
    { rewrite BEeq. unfold est_D, smD_bd. cbn [e_bw fst]. apply put_data_NZM. }
    assert (ROOM' : e_nblock e + bw_numZ (fst (smD_bd e znew znew znew znew znew znew znew)) <= ARR2_SIZE).
    { unfold est_D in ROOM. cbn [e_bw] in ROOM. exact ROOM. }
    pose (HFR := SDW (Z_to_bv 64 (1032 * smA_ng e)) w896 (Z_to_bv 64 (flag6 (smA_ng e))) w912 (Z_to_bv 64 (sm_nmtf e)) (Z_to_bv 64 (smA_ng e)) w936
                     (Z_to_bv 64 (18446744073709551615 - (c_E cx + 45448))) (Z_to_bv 64 (c_E cx + 45448)) (Z_to_bv 64 (c_E cx + 37708))
                     (Z_to_bv 64 (sm_alpha e)) (Z_to_bv 64 (smB_nsel e znew znew znew znew znew)) (Z_to_bv 64 (sm_alpha e))
                     (Z_to_bv 64 (c_E cx + 37708)) (Z_to_bv 64 (c_E cx + 51640)) (Z_to_bv 64 1) (Z_to_bv 64 1) w1024 (Z_to_bv 64 (c_A1 cx))).
    refine (U0_sd4_segC cx g e _ gp tp F fc (bv_unsigned sp - 1200) CX SEP GM GBS GZB HNB CEP PHI
                (bw_numZ (e_bw (est_D e znew znew znew znew znew znew znew))) ROOM znew BWOK
                znew znew znew znew znew znew m1 HFR J44 lo
                ra1 t0_1 t1_1 t2_1 s1_1 a0_1 a1_1 a2_1 a3_1 a4_1 a5_1 a6_1 a7_1 s2_1 s3_1 s4_1 s5_1 s6_1 s7_1 s8_1 s10_1 s11_1 t3_1 t4_1 t5_1 t6_1
                SDF SEL SLM LEN COD BLK eq_refl eq_refl eq_refl eq_refl eq_refl V816 V824 FJ44 L44' ST1a LO16 CLO MI1
                EH1e EH2e AR2' AR1 INU eq_refl eq_refl eq_refl eq_refl NLE _).
    intros m0' m2 H' i16' s2_2 s4_2 s5_2 s6_2 s7_2 s8_2 s10_2 s11_2 t4_2 t5_2 t6_2
           MA SRO ST2 MU2 WM2 F904 F928 F944 F960 F992 F1000 F1008 F1016 F1032 L16b BWE.
    rewrite BEeq in MA, BWE.
    pose proof MA as MAx. destruct MAx as (EH1d & EH2d & AR2d & HId & I16d & MId & MUd' & WMd).
    pose proof SRO as SROx. destruct SROx as (AR1d & INUd & SLMd & SELd & LENd & CODd & _).
    destruct (hc_split s0segs m2 (bv_unsigned sp - 1200) H' HId) as (K904 & K928 & K944 & K960 & K976 & K992 & K1024 & K1032).
    rewrite F904 in K904. rewrite F928 in K928. rewrite F944 in K944. rewrite F960 in K960.
    rewrite F992, F1000, F1008, F1016 in K992. rewrite F1032 in K1032.
    assert (K816 : rw_cells s0segs m2 (bv_unsigned sp - 1200 + 816)
                     [C8 (Z_to_bv 64 (c_E cx + 1704)); C8 (Z_to_bv 64 (18446744073709551615 - (c_E cx + 1704)))]).
    { eapply rw_cells_transport; [exact C816| exact MU2| exact WM2|].
      unfold sdWP. cbn [app disjoint_from cells_size csize Nat.add]. repeat split; lia. }
    assert (MD : MUd cx g (est_C e znew znew znew znew znew znew) (bv_unsigned sp - 1200) m2 (smD_b4 e znew znew znew znew znew znew znew) m2).
    { refine (conj EH1d (conj EH2d (conj AR2d (conj AR1d (conj LENd (conj CODd (conj K1032 (conj MId (conj _ _)))))))));
        [apply munch_refl| apply wmono_refl]. }
    refine (EMIT cx g e znew znew znew znew znew znew znew _ gp tp F fc (bv_unsigned sp - 1200) m2 m2 (h976 H') (h984 H') (h1024 H')
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                CX SEP GM GBS GZB HNB CEP PHI2 SDF BWE ROOM' MD SELd K816 K904 K928 K944 K960 K992 K976 K1024 _).
    intros m3 v976 v984 v1024 ra3 t0_3 t1_3 t2_3 s0_3 s1_3 a0_3 a1_3 a2_3 a3_3 a4_3 a5_3 a6_3 a7_3
           s2_3 s3_3 s4_3 s5_3 s6_3 s7_3 s8_3 s9_3 s10_3 s11_3 t3_3 t4_3 t5_3 t6_3 MUE C976 C1024 BWF.
    destruct (POST cx g e lo (bv_unsigned sp) sv m m1 m2 m3 m0' J0 Jm J3 Jx J44 Jf w16 w896 w912 w936 w1024 H' i16' v976 v984 v1024
                   s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra
                   GM GBS GZB EM AM CM MI ST LOW CLO AL CX SEP IMG BWOK HNB ROOM SFA SDF
                   EB1 AM1 CM1 MI1 ST1 MU1 WM1 L0 Lm L3 Lx L44 Lf FJ0 C16 FJm C816 FJ3 BLK FJx FJ44 FJf SAV
                   MA SRO ST2 MU2 WM2 L16b BWE MUE C976 C1024 BWF)
      as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10).
    eapply (U0_sm_epi _ gp tp F fc (bv_unsigned sp - 1200) m3 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra); [lia| exact PHI2| exact P10|].
    replace (bv_unsigned sp - 1200 + 1200) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
    apply evt_done. cbv beta.
    exists t0_3, t1_3, t2_3, a0_3, a1_3, a2_3, a3_3, a4_3, a5_3, a6_3, a7_3, t3_3, t4_3, t5_3, t6_3, m3.
    split; [reflexivity|].
    exact (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj P6 (conj P7 (conj P8 P9)))))))).
  Qed.
End SMT.

Theorem U0_sendMTF : sendMTF_spec.
Proof. exact (U0_sendMTF_gen U0_sd_emit_closed U0_sm_post). Qed.

End ACeilS1.
