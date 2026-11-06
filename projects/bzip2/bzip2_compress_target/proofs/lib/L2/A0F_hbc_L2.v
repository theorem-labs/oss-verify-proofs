(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout RT_iface D_defs D_kit I_read RT_liveprim.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require Import L2Kit L2Act L2StmtD A0_fs_L2f A0_sessK.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzLemmasHb BzHbW BzTac CmpMem AsanKit AsanCut A0F_hbc.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).

(* [comment removed for export] *)
Lemma ag32s_zero_prefix : forall ws (k : nat), (k <= length ws)%nat ->
  ag32s (repeat (Z_to_bv 64 0) k ++ skipn k ws) (fill0 (sv32 ws) 0 k) (Z.of_nat (length ws)).
Proof.
  intros ws k Hk i Hi. rewrite fill0_spec. unfold sv32, wnth.
  destruct (Z.ltb_spec i (0 + Z.of_nat k)); destruct (Z.leb_spec 0 i); cbn [andb]; try lia.
  - rewrite app_nth1 by (rewrite repeat_length; lia). rewrite nth_repeat_lt by lia. reflexivity.
  - rewrite app_nth2 by (rewrite repeat_length; lia). rewrite repeat_length, nth_skipn. do 2 f_equal. f_equal. lia.
Qed.

Section HBCL2.
Context {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MSET : memset_icontract RT e_asan_memset.
Hypothesis AF_PRIM : af_live_primary RT.   (* [comment removed for export] *)

Theorem hbCreateDecodeTables_cps : hbCreateDecodeTables_contract RT.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m DS t lws bws pws lbs minLen maxLen alpha lo usp LIM BASE PERM LEN W
         FDO MST A0E A1E A2E A3E A4E A5E A6E TP CEQ ARL LENl ARB LENb ARP LENp AR8 LEN8 DLIV D16 HT ART0 MI0 ST0 LOW LOR SPT SPA Halpha Hmm Hlen.
  intros T c Hc Hk.
  set (P := bv_unsigned sp + -64). assert (PE : P = usp - 64) by (unfold P, usp; lia).
  pose proof alloc_ceiling_range as ACR.
  pose proof LOR as LOR'. unfold RT_STACK in LOR'.
  pose proof (AF_PRIM Σ m _ _ ART0 DLIV ltac:(clear; lia)) as ID. unfold SEGTOP_A in ID.
  pose proof (af_live_range RT AF Σ m _ _ ART0 DLIV) as (DL0 & DL1 & _).
  pose proof (af_live_offshadow RT AF Σ m _ _ ART0 DLIV) as DOFF.
  assert (WCL : forall x, ~ outside W x -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x).
  { intros x Hx. unfold W, LIM, BASE, PERM in Hx. cbn [outside] in Hx. right; right; left. exists DS, 64144. split; [exact DLIV| clear - Hx HT; lia]. }
  destruct (act_setup_nf RT AF Σ m lo P usp W ART0 LOW ltac:(clear - PE LOR'; unfold RT_STACK; lia) ltac:(clear - PE; lia) SPT
              ltac:(clear - PE SPA; Z.div_mod_to_equations; lia) WCL) as (G & SOK).
  assert (HS : 0x61e000 <= DS /\ DS mod 16 = 0 /\ 0 <= t < 6) by (split; [exact ID| split; [exact D16| exact HT]]).
  assert (HLO : DS + 64144 <= lo /\ lo + 64 <= bv_unsigned sp) by (fold usp; clear - DL1 LOW LOR'; lia).
  assert (D8 : DS mod 8 = 0) by (clear - D16; Z.div_mod_to_equations; lia).
  assert (AFW1 : app_fp [(PERM, PERM + 1032); (P, bv_unsigned sp)]).
  { cbn [app_fp]. unfold SH_LO, SH_HI, PERM. fold usp. split; [clear - DOFF HT; lia|]. split; [right; clear - PE LOW LOR' CEQ ACR; lia| exact I]. }
  pose proof (live_reader RT AF Σ m DS 64144 _ ART0 DLIV D8 eq_refl AFW1) as SH1.
  destruct (fs_aconsts_of_art RT AF Σ m ART0) as [AC _].
  destruct (stk_split a0segs m lo P usp ST0 ltac:(clear - PE LOR'; lia)) as [ST0P _].
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ PMc _ T c MST Hc).
  eapply (A0_hbc_seg1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DS t lws bws pws lbs minLen maxLen alpha lo _ LENl LENb LENp LEN8 HS HLO Halpha Hmm Hlen m SH1);
    [exact ARP| exact AR8| exact ST0| exact (kmem_inv_N _ _ MI0)| exact AC| exact A0E| exact A1E| exact A2E| exact A3E| exact A4E| exact A5E| exact A6E|].
  clear Hc SH1 AC. unfold K1.
  intros m1 pwsF u0 u1 u2 e3 e4 e5 e6 e7 u3 u4 u5 u6 ARP1 LENP1 AGP AR81 FR1 ST1n MU1 WM1 NMI1. apply evt_done. intros c1 Hc1.
  destruct (after_l1 AF G Σ _ m m1 SOK ART0 MI0 ST0P (presi_refl _ _ _ _ m) NMI1 MU1 WM1
              ltac:(per_interval; [right; right; right; unfold W, PERM; cbn [outside]; lia| left; unfold P; lia])) as (ART1 & MI1 & ST1 & PR1 & _).
  pose proof (ck_intro P CStack) as KP. pose proof (ck_intro (bv_unsigned sp) CStack) as KU. pose proof (ck_intro DS (CLive DS 64144)) as KD.
  clear ST0 ST0P ARP AR8.
  unfold LIM, BASE, PERM, LEN in *.
  xfer_l1 m m1 MU1 WM1. clear NMI1 MU1 WM1 ST1n.
  (* [comment removed for export] *)
  pose proof (u32arr_bound _ _ _ _ ARB) as BB. rewrite LENb in BB.
  rewrite <- (firstn_skipn 23 bws) in ARB. apply (proj1 (u32arr_app _ _ _ _ _)) in ARB. destruct ARB as [ARB1 ARB2].
  rewrite firstn_length_le in ARB2 by (rewrite LENb; clear; lia).
  remember (skipn 23 bws) as bt eqn:Ebt.
  assert (LENbt : length bt = 235%nat) by (subst bt; rewrite length_skipn, LENb; reflexivity).
  clear ARB1.
  eapply (memset_call G PMc FDO MST Σ (DS + 51628 + 1032 * t) 92 z8 m1); [exact MSET| exact SOK| clear - DL0 DL1 HT ACR CEQ; lia| clear; lia| | exact ART1| exact MI1| exact ST1| exact Hc1|].
  { apply (cdst_live AF G Σ m1 DS 64144 _ 92 ART1 DLIV); clear - HT; lia. }
  clear Hc1. intros c2 m2 v0 v1 v2 f1 f2 f3 f4 f5 f6 f7 v3 v4 v5 v6 F2 fc2 Hc2 ART2 MI2 ST2 WM2 BY2 STEP2.
  pose proof (pres_step G Σ _ m1 m2 SOK PR1 STEP2 ltac:(per_interval; right; unfold W, BASE; cbn [outside]; lia)) as PR2.
  xfer_rt G SOK STEP2 WM2 m1 m2.
  rewrite (KMState.ret_pc_even 0x9e0cc ltac:(lia) eq_refl) in Hc2.
  assert (ARB : u32arr a0segs m2 (DS + 51628 + 1032 * t) (repeat (Z_to_bv 64 0) 23 ++ bt)).
  { destruct (af_acc_live RT AF Σ m2 DS 64144 ART2 DLIV) as [WRD _].
    pose proof (n_rw_CB_of_bytes m2 _ (repeat z8 (Z.to_nat 92)) BY2
                  ltac:(rewrite repeat_length; apply (wr_at_sub asegs m2 DS 64144 _ _ WRD); clear - HT; lia)) as ROW.
    rewrite repeat_length in ROW. change (Z.to_nat 92) with (4 * 23)%nat in ROW. change z8 with (Z_to_bv 8 0) in ROW.
    rewrite <- (u32s_repeat_zero 23) in ROW. apply u32arr_of_CB in ROW.
    apply u32arr_app. split; [exact ROW|]. rewrite repeat_length. exact ARB2. }
  clear BY2 STEP2 ARB2.
  assert (LENB1 : length (repeat (Z_to_bv 64 0) 23 ++ bt) = 258%nat) by (rewrite length_app, repeat_length, LENbt; reflexivity).
  assert (AGB1 : ag32s (repeat (Z_to_bv 64 0) 23 ++ bt) (hbm_base1 (sv32 bws)) 258).
  { unfold hbm_base1. subst bt. pose proof (ag32s_zero_prefix bws 23 ltac:(rewrite LENb; clear; lia)) as X. rewrite LENb in X. exact X. }
  (* [comment removed for export] *)
  assert (AFW2 : app_fp [(DS + 51628 + 1032 * t, DS + 51628 + 1032 * t + 1032)]).
  { cbn [app_fp]. unfold SH_LO, SH_HI. split; [clear - DOFF HT; lia| exact I]. }
  pose proof (live_reader RT AF Σ m2 DS 64144 _ ART2 DLIV D8 eq_refl AFW2) as SH2.
  eapply (l1_realizes RT AF Σ PMc _ T c2 MST Hc2).
  eapply (A0_hbc_seg2 sp gp tp s7 s8 s9 s10 s11 F2 fc2 DS t lws bws pws lbs minLen maxLen alpha lo _ LENl LENb LENp LEN8 HS HLO Halpha Hmm Hlen m2 SH2 _);
    [exact ARB| exact LENB1| exact AGB1| exact AR81| exact (kmem_inv_N _ _ MI2)|].
  clear Hc2 SH2 ARB AR81. unfold K2.
  intros m3 bws3 w0 w1 w2 g3 g4 g5 g6 g7 w3 w4 w5 w6 ARB3 LENB3 AGB3 AR83 MU3 WM3 NMI3. apply evt_done. intros c3 Hc3.
  destruct (after_l1 AF G Σ _ m2 m3 SOK ART2 MI2 ST2 PR2 NMI3 MU3 WM3
              ltac:(per_interval; right; right; right; unfold W, BASE; cbn [outside]; lia)) as (ART3 & MI3 & ST3 & PR3 & _).
  clear ST2.
  xfer_l1 m2 m3 MU3 WM3. clear NMI3 MU3 WM3.
  (* [comment removed for export] *)
  pose proof (u32arr_bound _ _ _ _ ARL) as BL. rewrite LENl in BL.
  rewrite <- (firstn_skipn 23 lws) in ARL. apply (proj1 (u32arr_app _ _ _ _ _)) in ARL. destruct ARL as [ARL1 ARL2].
  rewrite firstn_length_le in ARL2 by (rewrite LENl; clear; lia).
  remember (skipn 23 lws) as lt eqn:Elt.
  assert (LENlt : length lt = 235%nat) by (subst lt; rewrite length_skipn, LENl; reflexivity).
  clear ARL1.
  eapply (memset_call G PMc FDO MST Σ (DS + 45436 + 1032 * t) 92 z8 m3); [exact MSET| exact SOK| clear - DL0 DL1 HT ACR CEQ; lia| clear; lia| | exact ART3| exact MI3| exact ST3| exact Hc3|].
  { apply (cdst_live AF G Σ m3 DS 64144 _ 92 ART3 DLIV); clear - HT; lia. }
  clear Hc3. intros c4 m4 y0 y1 y2 h1 h2 h3 h4 h5 h6 h7 y3 y4 y5 y6 F4 fc4 Hc4 ART4 MI4 ST4 WM4 BY4 STEP4.
  pose proof (pres_step G Σ _ m3 m4 SOK PR3 STEP4 ltac:(per_interval; right; unfold W, LIM; cbn [outside]; lia)) as PR4.
  xfer_rt G SOK STEP4 WM4 m3 m4.
  rewrite (KMState.ret_pc_even 0x9e1b0 ltac:(lia) eq_refl) in Hc4.
  assert (ARL : u32arr a0segs m4 (DS + 45436 + 1032 * t) (repeat (Z_to_bv 64 0) 23 ++ lt)).
  { destruct (af_acc_live RT AF Σ m4 DS 64144 ART4 DLIV) as [WRD _].
    pose proof (n_rw_CB_of_bytes m4 _ (repeat z8 (Z.to_nat 92)) BY4
                  ltac:(rewrite repeat_length; apply (wr_at_sub asegs m4 DS 64144 _ _ WRD); clear - HT; lia)) as ROW.
    rewrite repeat_length in ROW. change (Z.to_nat 92) with (4 * 23)%nat in ROW. change z8 with (Z_to_bv 8 0) in ROW.
    rewrite <- (u32s_repeat_zero 23) in ROW. apply u32arr_of_CB in ROW.
    apply u32arr_app. split; [exact ROW|]. rewrite repeat_length. exact ARL2. }
  clear BY4 STEP4 ARL2.
  assert (LENL1 : length (repeat (Z_to_bv 64 0) 23 ++ lt) = 258%nat) by (rewrite length_app, repeat_length, LENlt; reflexivity).
  assert (AGL1 : ag32s (repeat (Z_to_bv 64 0) 23 ++ lt) (hbm_limit1 (sv32 lws)) 258).
  { unfold hbm_limit1. subst lt. pose proof (ag32s_zero_prefix lws 23 ltac:(rewrite LENl; clear; lia)) as X. rewrite LENl in X. exact X. }
  (* [comment removed for export] *)
  assert (AFW3 : app_fp [(DS + 45436 + 1032 * t, DS + 45436 + 1032 * t + 1032); (DS + 51628 + 1032 * t, DS + 51628 + 1032 * t + 1032); (P, bv_unsigned sp)]).
  { cbn [app_fp]. unfold SH_LO, SH_HI. fold usp. split; [clear - DOFF HT; lia|]. split; [clear - DOFF HT; lia|]. split; [right; clear - PE LOW LOR' CEQ ACR; lia| exact I]. }
  pose proof (live_reader RT AF Σ m4 DS 64144 _ ART4 DLIV D8 eq_refl AFW3) as SH3.
  eapply (l1_realizes RT AF Σ PMc _ T c4 MST Hc4).
  eapply (A0_hbc_seg3 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F4 fc4 DS t lws bws pws lbs minLen maxLen alpha lo _ LENl LENb LENp LEN8 HS HLO Halpha Hmm Hlen m4 SH3 _ _);
    [exact ARL| exact LENL1| exact AGL1| exact ARB3| exact LENB3| exact AGB3| exact FR1| exact ST4| exact (kmem_inv_N _ _ MI4)|].
  clear Hc4 SH3 ARL ARB3 FR1. unfold K3.
  intros m5 lwsF bwsF q0 q1 q2 b0 b1 b2 b3 b4 b5 b6 b7 q3 q4 q5 q6 ARLF LENLF AGLF ARBF LENBF AGBF ST5 MU5 WM5 NMI5. apply evt_done. intros c5 Hc5.
  destruct (after_l1 AF G Σ _ m4 m5 SOK ART4 MI4 ST4 PR4 NMI5 MU5 WM5
              ltac:(per_interval; [right; right; right; unfold W, LIM; cbn [outside]; lia| right; right; right; unfold W, BASE; cbn [outside]; lia| left; unfold P; lia]))
    as (ART5 & MI5 & _ & PR5 & _).
  clear ST4.
  xfer_l1 m4 m5 MU5 WM5. clear NMI5 MU5 WM5.
  (* [comment removed for export] *)
  apply Hk. exists Σ.
  split; [| split; [reflexivity| split; [reflexivity| split; reflexivity]]].
  eapply ASTA_conseq; [exact Hc5|]. intros ms <-.
  exists m5, q0, q1, q2, b0, b1, b2, b3, b4, b5, b6, b7, q3, q4, q5, q6, F4, fc4, lwsF, bwsF, pwsF.
  split; [reflexivity|]. split; [exact ART5|]. split; [exact MI5|]. split; [exact ST5|].
  split; [exact ARLF|]. split; [exact LENLF|]. split; [exact ARBF|]. split; [exact LENBF|]. split; [exact ARP1|]. split; [exact LENP1|].
  split; [rewrite (hb_create_pieces (uv8 lbs) alpha minLen maxLen); split; [exact AGLF| split; [exact AGBF| exact AGP]]|].
  exact (pres_final_nf RT AF Σ lo P usp W m m m5 ART0 LOW ltac:(clear - PE LOR'; lia) ltac:(clear - PE; lia) (munch_refl _ m) PR5).
Qed.
End HBCL2.
