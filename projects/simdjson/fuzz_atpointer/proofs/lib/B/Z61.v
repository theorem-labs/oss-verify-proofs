(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z10q FP Z119.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim StrFun Z3o.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import SjTape Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Z10v Zpp Zvw Rnd Zso Zvm.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks Zkt D_defs D_kit D_clx Z87 Sj_rtf Zpm Zpl Zq2
     Zq3 Zqc Zqd Zqb I_lkit Z45 Z5k Z3v Z3t Z5q Z60 Z63 Z65 Z62 Z64 Z5o.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section ObjKC.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RC2 : rt_contracts2 RT.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variable d : nat.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.

  Variable Σ1 : rts RT.
  Variable K : config -> Prop.
  Variables (m : mem) (fc : bv 32) (q b node i e c Kp Lk RA : Z) (kb : list byte) (gp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 : word) (od : list byte).
  Hypothesis LV : a_live RT Σ1 E.
  Hypothesis TY : ty (ae_T E) i = t_obj.
  Hypothesis NXT : tnext (ae_T E i) = e + 1.
  Hypothesis TILES : tiles (field (ae_T E) (ae_S E) (ae_sn E) (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d)) (i + 1) e c.
  Hypothesis I0 : 0 <= i.
  Hypothesis EN : e + 1 <= ae_n E - 1.
  Hypothesis LOB : ae_lo E + RT_STACK + 160 <= b.
  Hypothesis BQ : b + 152 <= q.
  Hypothesis QN : q <= node.
  Hypothesis NB : node + 16 <= ae_hi E.
  Hypothesis N8 : node mod 8 = 0.
  Hypothesis B32 : b mod 32 = 0.
  Hypothesis LKB : Z.of_nat (length kb) = Lk.
  Hypothesis KP0 : 0 < Kp.
  Hypothesis KPL : Kp + Lk <= ae_lo E.
  Hypothesis LK40 : Lk < 2^40.

  Definition PK (a : Z) : Prop := aclient (rt_live RT Σ1) (rt_frames RT Σ1) b a /\ ~ (b + 72 <= a < b + 96).

  Hypothesis CKP : forall m', ART RT Σ1 m' -> agree_on PK m m' -> checked_src RT Σ1 m' (wz (b + -144)) (ae_lo E) Kp Lk.
  Hypothesis KEYCL : forall a, Kp <= a < Kp + Lk -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) (b + -144) a.
  Hypothesis RA0 : 0 <= RA < 2^64.
  Hypothesis RA2 : RA mod 2 = 0.

  Hypothesis KF : forall (m' : mem) (F' : bvmap 5 word) (it j' : Z) (y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 : word),
    ART RT Σ1 m' -> mem_inv bsegs m' -> stk bsegs m' (ae_lo E) b -> AINV_A E m' -> agree_on PK m m' ->
    rw_cells bsegs m' node [C8 (wz (ae_DOC E)); C8 (wz i)] ->
    is_str (ae_T E) (ae_S E) (ae_sn E) it -> elem (ae_T E) (ae_S E) (ae_sn E) ck_any d (it + 1) j' -> i + 1 <= it -> j' <= e ->
    rw_cells bsegs m' (b + 72) [C8 (wz (ae_DOC E)); C8 (wz (it + 1)); C4 (Z_to_bv 64 0); CB 4 od] ->
    aevt RT PMc Σ1 K (MS (mkR (wz RA) (wz b) gp (wz TPV) y5 y6 y7 s0 (wz b) ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 s2 s3 s4 s5 s6 s7 s8 s9 s10 (wz 2147450880) y28 y29 y30 y31)
                     F' (wz RA) fc None m' (seg_rom bsegs)).

  Hypothesis KN : forall (m' : mem) (F' : bvmap 5 word) (y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 : word),
    ART RT Σ1 m' -> mem_inv bsegs m' -> stk bsegs m' (ae_lo E) b -> AINV_A E m' -> agree_on PK m m' ->
    rw_cells bsegs m' node [C8 (wz (ae_DOC E)); C8 (wz i)] ->
    rw_cells bsegs m' (b + 72) [CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 20); CB 4 od] ->
    aevt RT PMc Σ1 K (MS (mkR (wz RA) (wz b) gp (wz TPV) y5 y6 y7 s0 (wz b) ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 s2 s3 s4 s5 s6 s7 s8 s9 s10 (wz 2147450880) y28 y29 y30 y31)
                     F' (wz RA) fc None m' (seg_rom bsegs)).

  Local Ltac ul := lia_prep; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

  Let W : list (Z * Z) := atkey_W b (b + 72).
  Lemma kc_facts :
    (forall Σx, fp_client RT Σx (ae_lo E) W)
    /\ Forall (fun r => ae_lo E <= fst r) W
    /\ (forall mx m', ART RT Σ1 mx -> munch W mx m' -> wmono bsegs mx m' -> ART RT Σ1 m')
    /\ (forall mx m', AINV_A E mx -> munch W mx m' -> wmono bsegs mx m' -> AINV_A E m')
    /\ (forall mx, ART RT Σ1 mx -> shz mx (ae_TAPE E) (8 * ae_n E))
    /\ (forall mx, ART RT Σ1 mx -> shz mx (ae_SBUF E) (ae_NS E))
    /\ (forall mx, ART RT Σ1 mx -> shz mx node 16)
    /\ (forall mx, ART RT Σ1 mx -> shz mx (b + 72) 24)
    /\ bv_unsigned (Z_to_bv 64 (b + -144)) = b + -144.
  Proof using AF OK LV LOB BQ QN NB N8 B32.
    clear KF KN CKP KEYCL RA0 RA2 LKB KP0 KPL LK40 TY NXT TILES I0 EN.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) (SB16 & NS8 & SN & SS & SL) PTRR P0' (D8 & DF & DL & DS & DT) LOW [HL HT]].
    pose proof LV as (LVT & LVS & LVP & LVF & LWIN).
    assert (FPW : forall Σx, fp_client RT Σx (ae_lo E) W) by (intros Σx; unfold W, atkey_W; apply fp_client_stack2; ul).
    assert (HWlo : Forall (fun r => ae_lo E <= fst r) W) by (unfold W, atkey_W; constructor; [cbn; ul|]; constructor; [cbn; ul| constructor]).
    split; [exact FPW|]. split; [exact HWlo|].
    split; [intros mx m' HA MU WM; exact (lvl_art_munch RT AF E Σ1 _ mx m' HA LV (FPW Σ1) MU WM)|].
    split; [intros mx m' AI MU WM; exact (AINV_A_munch E _ mx m' OK AI MU HWlo)|].
    split; [intros mx HA; exact (lvl_shz_tape RT AF E OK Σ1 mx HA LV)|].
    split.
    { intros mx HA. pose proof (shz_live RT AF Σ1 mx _ _ HA LVS ltac:(clear - SB16; Z.div_mod_to_equations; lia)) as X.
      replace (8 * (ae_NS E / 8)) with (ae_NS E) in X by (clear - NS8; Z.div_mod_to_equations; lia). exact X. }
    split; [intros mx HA; apply (lvl_shz_rec RT AF E OK Σ1 mx node 16 HA LV); first [ul | reflexivity | exact N8]|].
    split; [intros mx HA; apply (lvl_shz_rec RT AF E OK Σ1 mx (b + 72) 24 HA LV); first [ul | reflexivity | clear - B32; Z.div_mod_to_equations; lia]|].
    apply unsigned_lit. ul.
  Qed.

  Lemma PK_outside_W : forall mx x, ART RT Σ1 mx -> PK x -> outside W x.
  Proof using AF OK LV LOB BQ.
    intros mx x HA [Hx Ho]. unfold W, atkey_W. cbn [outside]. split; [| split; [clear - Ho; lia| exact Logic.I]].
    pose proof LV as (_ & _ & _ & _ & LWIN).
    destruct (aclient_split_c RT AF Σ1 mx b x HA Hx) as [H|H]; [clear - H; lia|].
    pose proof (ok_lo E OK). unfold RT_STACK in LOB. clear - H LOB LWIN H0. lia.
  Qed.

  Lemma PK_of_pres : forall mx m' dst n, rt_pres_ex (rt_live RT Σ1) (rt_frames RT Σ1) (b + -144) dst n mx m' ->
    (forall a, dst <= a < dst + n -> b + 72 <= a < b + 96) -> agree_on PK mx m'.
  Proof.
    intros mx m' dst n PR Hd. apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PR). intros x [Hx Ho]. split.
    - apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto| auto| lia].
    - intros Hn. exact (Ho (Hd _ Hn)).
  Qed.

  Lemma atkey_nfK : forall (m1 : mem) (F1 : bvmap 5 word) (x5 x6 x7 xs0 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31 : word)
      (jlo oa ob oc : list byte),
    ART RT Σ1 m1 -> mem_inv bsegs m1 -> stk bsegs m1 (ae_lo E) (b + -144) -> AINV_A E m1 -> agree_on PK m m1 ->
    rw_cells bsegs m1 node [C8 (wz (ae_DOC E)); C8 (wz i)] ->
    rw_cells bsegs m1 (b + -144) (CB 40 jlo :: atkey_saved (wz RA) s0 (wz b) s2 s3 s4 s5 s6 s7 s8 s9 s10 (wz 2147450880)) ->
    rw_cells bsegs m1 (b + 72) [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] ->
    aevt RT PMc Σ1 K (MS (mkR (wz 0x9a718) (wz (b + -144)) gp (wz TPV) x5 x6 x7 xs0 (wz (b + 72 + 16)) (wz (b + 72)) (wz 0) (wz 16) xa3 xa4 xa5 xa6 xa7
                         xs2 xs3 xs4 xs5 xs6 (wz 2147450880) xs8 xs9 xs10 xs11 x28 x29 x30 x31) F1 (wz e_asan_memset) fc None m1 (seg_rom bsegs)).
  Proof using AF RC2 OK FDO MST LV LOB BQ QN NB N8 B32 RA0 RA2 KN KP0 kb LKB.
    intros until oc. intros ART1 MI1 ST1 AI1 AG1 NODE1 FR1 OUT1. clear LKB LK40 KPL CKP KEYCL KF TY NXT TILES I0 EN.
    pose proof kc_facts as (FPW & HWlo & ARTW & AIW & SHZTg & SHZSg & SHZNg & SHZOg & EU).
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) (SB16 & NS8 & SN & SS & SL) PTRR P0' (D8 & DF & DL & DS & DT) LOW [HL HT]].
    pose proof LV as (LVT & LVS & LVP & LVF & LWIN). pose proof (rc2_rt RT RC2) as RC.
    pose proof (af_sp0_range RT AF Σ1 m1 ART1) as SP0R.
    assert (CDST : checked_dst RT Σ1 m1 (Z_to_bv 64 (b + -144)) (b + 72) 16).
    { apply (checked_dst_stack RT AF Σ1 m1 _ (b + 72) 16 ART1); [ul| ul| rewrite EU; lia|].
      apply (wr_at_sub m1 (b + 72) 24 (b + 72) 16); [| lia| lia| lia]. pose proof (proj2 OUT1) as X. cbn [cells_size csize Nat.add] in X. exact X. }
    pose proof (call_ok_lvl RT E OK Σ1 m1 (b + -144) LV ST1 ltac:(ul) ltac:(ul) ltac:(clear - B32; Z.div_mod_to_equations; lia)) as COK.
    eapply (aevt_memsetP RT RC PMc FDO MST Σ1 K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc m1 (b + 72) 16 (Z_to_bv 8 0) (ae_lo E));
      [reflexivity| reflexivity| reflexivity| ul| lia| exact CDST| exact ART1| exact MI1| exact COK|].
    intros t0' t1' t2' g1 g2 g3 g4 g5 g6 g7 t3' t4' t5' t6' F2 m2 (ART2 & MI2 & WM2 & ST2) PRES2 BY2.
    rewrite EU in ST2, PRES2. change (Z.to_nat 16) with 16%nat in BY2.
    rewrite (ret_pc_even 0x9a718) by (clear; lia).
    assert (AG2 : agree_on (fun x => aclient (rt_live RT Σ1) (rt_frames RT Σ1) (b + -144) x /\ ~ (b + 72 <= x < b + 72 + 16)) m1 m2).
    { apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES2). intros x Hx. exact Hx. }
    pose proof (PK_of_pres m1 m2 (b + 72) 16 PRES2 ltac:(intros a Ha; lia)) as AG12.
    assert (FR2 : rw_cells bsegs m2 (b + -144) (CB 40 jlo :: atkey_saved (wz RA) s0 (wz b) s2 s3 s4 s5 s6 s7 s8 s9 s10 (wz 2147450880))).
    { apply (rw_cells_agree_nw bsegs m1 m2 _ _ FR1). eapply agree_sub; [exact AG2|]. intros x Hx. unfold atkey_saved in Hx. cbn [cells_size csize Nat.add app length] in Hx. cbv beta.
      split; [left; ul| clear - Hx; lia]. }
    assert (NODE2 : rw_cells bsegs m2 node [C8 (wz (ae_DOC E)); C8 (wz i)]).
    { apply (rw_cells_agree_nw bsegs m1 m2 _ _ NODE1). eapply agree_sub; [exact AG2|]. intros x Hx. cbn [cells_size csize Nat.add app length] in Hx. cbv beta.
      split; [left; ul| clear - Hx BQ QN; lia]. }
    pose proof (rec_copy16 m1 m2 (b + 72) [CB 8 oa; CB 8 ob] (CB 4 oc) od (repeat (Z_to_bv 8 0) 16) _ _ _ OUT1 eq_refl eq_refl BY2 eq_refl WM2 PRES2 ltac:(lia) ltac:(ul)) as OUT2.
    pose proof (AINV_A_pres_ex RT Σ1 E _ (b + 72) 16 m1 m2 LV OK AI1 PRES2 ltac:(ul)) as AI2.
    apply (aevt_evt RT AF PMc MST).
    eapply (atkey_after_nf E OK _ m2 F2 fc b (b + 72) RA gp s0 (wz b) s2 s3 s4 s5 s6 s7 s8 s9 s10 (wz 2147450880) jlo (repeat (Z_to_bv 8 0) 16) oc od);
      [exact FR2| exact ST2| exact MI2| ul| exact OUT2| lia| ul| clear - B32; Z.div_mod_to_equations; lia| exact (SHZOg m2 ART2)| exact RA0| exact RA2|].
    intros m3 y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 MU3 WM3 MI3 ST3 OUT3. apply evt_done.
    assert (ART3 : ART RT Σ1 m3) by (apply (lvl_art_munch RT AF E Σ1 [(b + 72, b + 72 + 24)] m2 m3 ART2 LV); [apply fp_client_stack1; ul| exact MU3| exact WM3]).
    apply (KN m3 F2); [exact ART3| exact MI3| exact ST3| | | | exact OUT3].
    - apply (AINV_A_munch E [(b + 72, b + 72 + 24)] m2 m3 OK AI2 MU3). constructor; [cbn; ul| constructor].
    - eapply agree_trans; [exact AG1|]. eapply agree_trans; [exact AG12|].
      apply (agree_of_munch _ _ _ _ MU3). intros x [Hx Ho]. cbn [outside]. split; [clear - Ho; lia| exact Logic.I].
    - apply (rw_cells_agree_nw bsegs m2 m3 _ _ NODE2). apply (agree_of_munch _ _ _ _ MU3). intros x Hx. cbn [cells_size csize Nat.add app length] in Hx.
      cbn [outside]. split; [clear - Hx BQ QN; lia| exact Logic.I].
  Qed.

  Definition sbuf_bytesB (o l : Z) : list byte := firstn (Z.to_nat l) (skipn (Z.to_nat (o + 4)) (map (Z_to_bv 8) (ae_sbs E))).
  Lemma sbuf_bytesB_at : forall mx o l, bytes_at bsegs mx (ae_SBUF E) (map (Z_to_bv 8) (ae_sbs E)) -> 0 <= o -> 0 <= l -> o + 4 + l < ae_sn E ->
    bytes_at bsegs mx (ae_SBUF E + o + 4) (sbuf_bytesB o l) /\ length (sbuf_bytesB o l) = Z.to_nat l.
  Proof.
    intros mx o l HB Ho Hl Hol. unfold sbuf_bytesB. split.
    - replace (ae_SBUF E + o + 4) with (ae_SBUF E + Z.of_nat (Z.to_nat (o + 4))) by lia.
      apply bytes_at_firstn. apply bytes_at_skipn; [exact HB|]. rewrite length_map. lia.
    - rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn, length_map. lia.
  Qed.

  Lemma atkey_loopK : forall (n : nat) (it c' : Z) (mx : mem) (Fx : bvmap 5 word)
      (x1 x5 x6 x7 xa0 xa1 xa2 xa3 xa4 x15 x16 x17 xs6 x28 x29 x30 x31 : word) (j0 oa ob oc : list byte),
    tiles (field (ae_T E) (ae_S E) (ae_sn E) (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d)) it e c' -> it <> e -> i + 1 <= it -> e - it <= Z.of_nat n ->
    ART RT Σ1 mx -> mem_inv bsegs mx -> stk bsegs mx (ae_lo E) (b + -144) -> AINV_A E mx -> agree_on PK m mx ->
    rw_cells bsegs mx node [C8 (wz (ae_DOC E)); C8 (wz i)] ->
    rw_cells bsegs mx (b + -144) (atkey_frame j0 (b + 72) Kp (wz RA) s0 (wz b) s2 s3 s4 s5 s6 s7 s8 s9 s10 (wz 2147450880)) ->
    rw_cells bsegs mx (b + 72) [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] ->
    bytes_at bsegs mx Kp kb ->
    aevt RT PMc Σ1 K (MS (mkR x1 (wz (b + -144)) gp (wz TPV) x5 x6 x7 (wz 67240448) (wz Lk) xa0 xa1 xa2 xa3 xa4 x15 x16 x17
                         (wz 1) (wz (ae_DOC E)) (wz it) (wz (ae_DOC E + 8)) xs6 (wz 2147450880) (wz e) (wz 32) (wz 72057594037927935)
                         (wz ((ae_DOC E + 8) / 8 + 2147450880)) x28 x29 x30 x31) Fx (wz 0x9a7b8) fc None mx (seg_rom bsegs)).
  Proof using AF RC2 OK FDO MST LV TY NXT TILES I0 EN LOB BQ QN NB N8 B32 LKB KP0 KPL LK40 CKP KEYCL RA0 RA2 KF KN kb.
    pose proof kc_facts as (FPW & HWlo & ARTW & AIW & SHZTg & SHZSg & SHZNg & SHZOg & EU).
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) (SB16 & NS8 & SN & SS & SL) PTRR P0' (D8 & DF & DL & DS & DT) LOW [HL HT]].
    pose proof LV as (LVT & LVS & LVP & LVF & LWIN). pose proof (rc2_rt RT RC2) as RC.
    pose proof (tape_wf_root _ _ _ _ _ WF) as [_ NR].
    assert (HSN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).

    assert (TRN : forall my m2, ART RT Σ1 my -> munch W my m2 -> wmono bsegs my m2 ->
              rw_cells bsegs my node [C8 (wz (ae_DOC E)); C8 (wz i)] -> rw_cells bsegs m2 node [C8 (wz (ae_DOC E)); C8 (wz i)]).
    { intros my m2 HA MU WM ND. apply (rw_cells_agree_nw bsegs my m2 _ _ ND). apply (agree_of_munch _ _ _ _ MU).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. unfold W, atkey_W. cbn [outside]. clear - Hx BQ QN. lia. }
    assert (TRK : forall my m2, munch W my m2 -> bytes_at bsegs my Kp kb -> bytes_at bsegs m2 Kp kb).
    { intros my m2 MU KB. apply (bytes_at_transport bsegs W my m2 Kp kb KB MU). unfold W, atkey_W. cbn [disjoint_from fst snd]. rewrite LKB.
      pose proof LOW. unfold RT_STACK in LOB. clear - KP0 KPL LOB H. lia. }
    assert (TRA : forall my m2, ART RT Σ1 my -> agree_on PK m my -> munch W my m2 -> agree_on PK m m2).
    { intros my m2 HA AG MU. eapply agree_trans; [exact AG|]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. exact (PK_outside_W my x HA Hx). }
    induction n as [|n IH]; intros until oc; intros TI NE IT FUEL ARTx MIx STx AIx AGx NODEx FRx OUTx KEYx.
    { pose proof (tiles_le _ (field_lt _ _ _ _ (elem_lt _ _ _ _ d)) _ _ _ TI). lia. }
    destruct (object_iter _ _ _ _ (fun c0 cv H => H) HSN d it e c' TI NE ltac:(lia) ltac:(lia)) as (j' & STR & EL & IJ & AFT & TI').

    assert (NEXTK : forall (my : mem) (Fy : bvmap 5 word) (y1 y5 y6 y7 ya0 ya1 ya2 ya3 ya4 y15 y16 y17 ys6 y28 y29 y30 y31 : word),
      ART RT Σ1 my -> mem_inv bsegs my -> stk bsegs my (ae_lo E) (b + -144) -> AINV_A E my -> agree_on PK m my ->
      rw_cells bsegs my node [C8 (wz (ae_DOC E)); C8 (wz i)] ->
      rw_cells bsegs my (b + -144) (atkey_frame j0 (b + 72) Kp (wz RA) s0 (wz b) s2 s3 s4 s5 s6 s7 s8 s9 s10 (wz 2147450880)) ->
      rw_cells bsegs my (b + 72) [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] -> bytes_at bsegs my Kp kb ->
      aevt RT PMc Σ1 K (MS (mkR y1 (wz (b + -144)) gp (wz TPV) y5 y6 y7 (wz 67240448) (wz Lk) ya0 ya1 ya2 ya3 ya4 y15 y16 y17
                           (wz 1) (wz (ae_DOC E)) (wz it) (wz (ae_DOC E + 8)) ys6 (wz 2147450880) (wz e) (wz 32) (wz 72057594037927935)
                           (wz ((ae_DOC E + 8) / 8 + 2147450880)) y28 y29 y30 y31) Fy (wz 0x9a8ac) fc None my (seg_rom bsegs))).
    { intros until y31. intros ARTy MIy STy AIy AGy NODEy FRy OUTy KEYy.
      apply (aevt_evt RT AF PMc MST).
      eapply (atkey_nextseg E OK d _ my my Fy fc b (b + 72) Kp Lk e it j');
        [ exact EN| exact EL| lia| lia
        | intros m' MU WM; exact (AIW my m' AIy MU WM)
        | intros m' MU WM; exact (shb_cells_of_art RT AF Σ1 m' (ARTW my m' ARTy MU WM))
        | intros m' MU WM; exact (lvl_shz_doc E OK m' (AIW my m' AIy MU WM))
        | intros m' MU WM; exact (SHZTg m' (ARTW my m' ARTy MU WM))
        | ul| ul| clear - B32; Z.div_mod_to_equations; lia| lia| ul| clear - B32; Z.div_mod_to_equations; lia
        | apply munch_refl| apply wmono_refl| exact MIy| exact STy| exact FRy| exact OUTy| | ].
      -
        intros m2 z1 za0 za1 za2 za3 za4 zs6 MU2 WM2 MI2 ST2 FR2 OUT2 NE2. apply evt_done.
        pose proof (ARTW my m2 ARTy MU2 WM2) as ART2.
        eapply (IH j' (c' - 1) m2 Fy); [exact TI'| exact NE2| lia| lia| exact ART2| exact MI2| exact ST2| exact (AIW my m2 AIy MU2 WM2)
          | exact (TRA my m2 ARTy AGy MU2)| exact (TRN my m2 ARTy MU2 WM2 NODEy)| exact FR2| exact OUT2| exact (TRK my m2 MU2 KEYy)].
      -
        intros m2 za3 za4 zs4 zs6 MU2 WM2 MI2 ST2 FR2 OUT2. apply evt_done.
        unfold atkey_frame, atkey_saved in FR2. cbn [app] in FR2.
        lazymatch type of FR2 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
          pose proof (rw_cells_merge bsegs m2 (b + -144) [] [c0; c1; c2; c3; c4] rest FR2) as FR2' end.
        cbn [app cells_size csize Nat.add] in FR2'.
        eapply (atkey_nfK m2 Fy); [exact (ARTW my m2 ARTy MU2 WM2)| exact MI2| exact ST2| exact (AIW my m2 AIy MU2 WM2)| exact (TRA my m2 ARTy AGy MU2)
          | exact (TRN my m2 ARTy MU2 WM2 NODEy)| unfold atkey_saved; exact FR2'| exact OUT2]. }

    assert (FOUNDK : forall (my : mem) (Fy : bvmap 5 word) (y5 y6 y7 ys0 ys1 ys2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys5 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 y31 : word),
      ART RT Σ1 my -> mem_inv bsegs my -> stk bsegs my (ae_lo E) (b + -144) -> AINV_A E my -> agree_on PK m my ->
      rw_cells bsegs my node [C8 (wz (ae_DOC E)); C8 (wz i)] ->
      rw_cells bsegs my (b + -144) (atkey_frame j0 (b + 72) Kp (wz RA) s0 (wz b) s2 s3 s4 s5 s6 s7 s8 s9 s10 (wz 2147450880)) ->
      rw_cells bsegs my (b + 72) [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] ->
      aevt RT PMc Σ1 K (MS (mkR (wz 0x9a8a8) (wz (b + -144)) gp (wz TPV) y5 y6 y7 ys0 ys1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
                           ys2 (wz (ae_DOC E)) (wz it) ys5 ys6 (wz 2147450880) ys8 ys9 ys10 ys11 y28 y29 y30 y31) Fy (wz 0x9a95c) fc None my (seg_rom bsegs))).
    { intros until y31. intros ARTy MIy STy AIy AGy NODEy FRy OUTy.
      apply (aevt_evt RT AF PMc MST). unfold atkey_frame in FRy.
      eapply (atkey_found E OK _ my Fy fc b (b + 72) RA it Kp);
        [ exact FRy| exact STy| exact MIy| ul| exact OUTy| lia| ul| clear - B32; Z.div_mod_to_equations; lia
        | intros m' MU WM; apply (SHZOg m'); apply (lvl_art_munch RT AF E Σ1 [(b + 72, b + 72 + 24)] my m' ARTy LV); [apply fp_client_stack1; ul| exact MU| exact WM]
        | exact RA0| exact RA2| lia| lia| ].
      intros m2 z5 z6 z7 za0 za1 za2 za3 za4 za5 za6 za7 z28 z29 z30 z31 MU2 WM2 MI2 ST2 OUT2. apply evt_done.
      assert (ART2 : ART RT Σ1 m2) by (apply (lvl_art_munch RT AF E Σ1 [(b + 72, b + 72 + 24)] my m2 ARTy LV); [apply fp_client_stack1; ul| exact MU2| exact WM2]).
      apply (KF m2 Fy it j'); [exact ART2| exact MI2| exact ST2| | | | exact STR| exact EL| lia| lia| exact OUT2].
      - apply (AINV_A_munch E [(b + 72, b + 72 + 24)] my m2 OK AIy MU2). constructor; [cbn; ul| constructor].
      - eapply agree_trans; [exact AGy|]. apply (agree_of_munch _ _ _ _ MU2). intros x [Hx Ho]. cbn [outside]. split; [clear - Ho; lia| exact Logic.I].
      - apply (rw_cells_agree_nw bsegs my m2 _ _ NODEy). apply (agree_of_munch _ _ _ _ MU2). intros x Hx. cbn [cells_size csize Nat.add app length] in Hx.
        cbn [outside]. split; [clear - Hx BQ QN; lia| exact Logic.I]. }

    apply (aevt_evt RT AF PMc MST).
    eapply (atkey_headseg E OK _ mx mx Fx fc b (b + 72) Kp Lk e it);
      [ exact EN| exact STR| lia| lia| lia| pose proof LOW; ul
      | intros m' MU WM; exact (AIW mx m' AIx MU WM)
      | intros m' MU WM; exact (shb_cells_of_art RT AF Σ1 m' (ARTW mx m' ARTx MU WM))
      | intros m' MU WM; exact (lvl_shz_doc E OK m' (AIW mx m' AIx MU WM))
      | intros m' MU WM; exact (SHZTg m' (ARTW mx m' ARTx MU WM))
      | intros m' MU WM; exact (SHZSg m' (ARTW mx m' ARTx MU WM))
      | ul| ul| clear - B32; Z.div_mod_to_equations; lia| lia| ul| clear - B32; Z.div_mod_to_equations; lia
      | apply munch_refl| apply wmono_refl| exact MIx| exact STx| exact FRx| exact OUTx| | ].
    {
      intros m2 l za0 za1 za2 za3 za4 SA NEQ MU2 WM2 MI2 ST2 FR2 OUT2. apply evt_done.
      apply (NEXTK m2 Fx); [exact (ARTW mx m2 ARTx MU2 WM2)| exact MI2| exact ST2| exact (AIW mx m2 AIx MU2 WM2)| exact (TRA mx m2 ARTx AGx MU2)
        | exact (TRN mx m2 ARTx MU2 WM2 NODEx)| exact FR2| exact OUT2| exact (TRK mx m2 MU2 KEYx)]. }

    intros m2 l za3 za4 SA ELK MU2 WM2 MI2 ST2 FR2 OUT2. apply evt_done.
    pose proof (ARTW mx m2 ARTx MU2 WM2) as ART2. pose proof (AIW mx m2 AIx MU2 WM2) as AI2. pose proof (TRA mx m2 ARTx AGx MU2) as AG2.
    pose proof (TRN mx m2 ARTx MU2 WM2 NODEx) as NODE2. pose proof (TRK mx m2 MU2 KEYx) as KEY2. clear MU2 WM2.
    pose proof (af_sp0_range RT AF Σ1 m2 ART2) as SP0R.
    pose proof (call_ok_lvl RT E OK Σ1 m2 (b + -144) LV ST2 ltac:(ul) ltac:(ul) ltac:(clear - B32; Z.div_mod_to_equations; lia)) as COK2.
    pose proof (str_at_bounds _ _ HSN _ _ SA) as (O0 & L0b & OL & LE & O56).
    set (o := tval (ae_T E it)) in *.

    assert (RET : forall (m3 : mem) (F3 : bvmap 5 word) (r y5 y6 y7 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y28 y29 y30 y31 : word),
      ART RT Σ1 m3 -> mem_inv bsegs m3 -> stk bsegs m3 (ae_lo E) (b + -144) -> AINV_A E m3 -> agree_on PK m m3 ->
      rw_cells bsegs m3 node [C8 (wz (ae_DOC E)); C8 (wz i)] ->
      rw_cells bsegs m3 (b + -144) (atkey_frame j0 (b + 72) Kp (wz RA) s0 (wz b) s2 s3 s4 s5 s6 s7 s8 s9 s10 (wz 2147450880)) ->
      rw_cells bsegs m3 (b + 72) [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] -> bytes_at bsegs m3 Kp kb ->
      aevt RT PMc Σ1 K (MS (mkR (wz 0x9a8a8) (wz (b + -144)) gp (wz TPV) y5 y6 y7 (wz 67240448) (wz Lk) r ya1 ya2 ya3 ya4 ya5 ya6 ya7
                           (wz 1) (wz (ae_DOC E)) (wz it) (wz (ae_DOC E + 8)) xs6 (wz 2147450880) (wz e) (wz 32) (wz 72057594037927935)
                           (wz ((ae_DOC E + 8) / 8 + 2147450880)) y28 y29 y30 y31) F3 (wz 0x9a8a8) fc None m3 (seg_rom bsegs))).
    { intros until y31. intros ART3 MI3 ST3 AI3 AG3 NODE3 FR3 OUT3 KEY3.
      apply (aevt_evt RT AF PMc MST). unfold atkey_frame, atkey_saved in FR3. cbn [app] in FR3.
      pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl bsegs m3) as WM.
      step. if_cases Kr; zify_cond Kr.
      - eapply evt_eq; [| apply evt_done; apply (FOUNDK m3 F3); [exact ART3| exact MI3| exact ST3| exact AI3| exact AG3| exact NODE3| unfold atkey_frame, atkey_saved; cbn [app]; exact FR3| exact OUT3]].
        atp_st_eq.
      - apply evt_done. apply (NEXTK m3 F3); [exact ART3| exact MI3| exact ST3| exact AI3| exact AG3| exact NODE3| unfold atkey_frame, atkey_saved; cbn [app]; exact FR3| exact OUT3| exact KEY3]. }
    destruct (Z.eq_dec Lk 0) as [LK0|LKP].
    -
      eapply (aevt_memcmp0 RT PMc FDO MST RC2 Σ1); [rewrite LK0; reflexivity| exact ART2| exact MI2| exact COK2|].
      intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F3 m3 (ART3 & MI3 & WM3 & ST3) PR3.
      rewrite EU in ST3, PR3. rewrite (ret_pc_even 0x9a8a8) by (clear; lia).
      assert (AG23 : agree_on (fun x => aclient (rt_live RT Σ1) (rt_frames RT Σ1) (b + -144) x /\ ~ (0 <= x < 0 + 0)) m2 m3).
      { apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PR3). intros x Hx. exact Hx. }
      apply (RET m3 F3); [exact ART3| exact MI3| exact ST3| apply (AINV_A_agree E m2 m3 AI2); eapply agree_sub; [exact AG23| intros x Hx; cbv beta; split; [exact (ainv_rng_aclient RT Σ1 E (b + -144) x LV OK Hx)| clear; lia]]
        | eapply agree_trans; [exact AG2| exact (PK_of_pres m2 m3 0 0 PR3 ltac:(intros a Ha; lia))]| | | | ].
      + apply (rw_cells_agree_nw bsegs m2 m3 _ _ NODE2). eapply agree_sub; [exact AG23|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. split; [left; ul| clear - Hx; lia].
      + apply (rw_cells_agree_nw bsegs m2 m3 _ _ FR2). eapply agree_sub; [exact AG23|]. intros x Hx. unfold atkey_frame, atkey_saved in Hx. cbn [cells_size csize Nat.add app length] in Hx. cbv beta.
        split; [left; ul| clear - Hx; lia].
      + apply (rw_cells_agree_nw bsegs m2 m3 _ _ OUT2). eapply agree_sub; [exact AG23|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. split; [left; ul| clear - Hx; lia].
      + apply (bytes_at_agree bsegs m2 m3 _ _ KEY2). eapply agree_sub; [exact AG23|]. intros x Hx. rewrite LKB in Hx. cbv beta. split; [apply KEYCL; exact Hx| clear - Hx; lia].
    -
      destruct (sbuf_bytesB_at m2 o Lk (proj1 (proj2 AI2)) ltac:(lia) ltac:(lia) ltac:(lia)) as [QB QL].
      assert (LKN : length kb = Z.to_nat Lk) by lia.
      eapply (aevt_memcmpW RT PMc FDO MST RC2 Σ1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fx fc m2 Kp (ae_SBUF E + o + 4) kb (sbuf_bytesB o Lk) (ae_lo E));
        [reflexivity| reflexivity| rewrite LKB; reflexivity| rewrite QL, LKN; reflexivity| pose proof LOW; ul| ul| rewrite LKN; lia| rewrite LKB; exact LK40
        | exact KEY2| exact QB| rewrite LKB; exact (CKP m2 ART2 AG2)| | exact ART2| exact MI2| exact COK2|].
      { rewrite LKB. apply (checked_src_live RT AF Σ1 m2 _ (ae_lo E) (ae_SBUF E) (ae_NS E) _ _ ART2 LVS); [lia| lia| ul]. }
      intros r t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F3 m3 HR (ART3 & MI3 & WM3 & ST3) PR3.
      rewrite EU in ST3, PR3. rewrite (ret_pc_even 0x9a8a8) by (clear; lia).
      assert (AG23 : agree_on (fun x => aclient (rt_live RT Σ1) (rt_frames RT Σ1) (b + -144) x /\ ~ (0 <= x < 0 + 0)) m2 m3).
      { apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PR3). intros x Hx. exact Hx. }
      apply (RET m3 F3); [exact ART3| exact MI3| exact ST3| apply (AINV_A_agree E m2 m3 AI2); eapply agree_sub; [exact AG23| intros x Hx; cbv beta; split; [exact (ainv_rng_aclient RT Σ1 E (b + -144) x LV OK Hx)| clear; lia]]
        | eapply agree_trans; [exact AG2| exact (PK_of_pres m2 m3 0 0 PR3 ltac:(intros a Ha; lia))]| | | | ].
      + apply (rw_cells_agree_nw bsegs m2 m3 _ _ NODE2). eapply agree_sub; [exact AG23|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. split; [left; ul| clear - Hx; lia].
      + apply (rw_cells_agree_nw bsegs m2 m3 _ _ FR2). eapply agree_sub; [exact AG23|]. intros x Hx. unfold atkey_frame, atkey_saved in Hx. cbn [cells_size csize Nat.add app length] in Hx. cbv beta.
        split; [left; ul| clear - Hx; lia].
      + apply (rw_cells_agree_nw bsegs m2 m3 _ _ OUT2). eapply agree_sub; [exact AG23|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. split; [left; ul| clear - Hx; lia].
      + apply (bytes_at_agree bsegs m2 m3 _ _ KEY2). eapply agree_sub; [exact AG23|]. intros x Hx. rewrite LKB in Hx. cbv beta. split; [apply KEYCL; exact Hx| clear - Hx; lia].
  Qed.

  Theorem obj_atkeyB : forall (F : bvmap 5 word) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (oa ob oc : list byte),
    ART RT Σ1 m -> mem_inv bsegs m -> stk bsegs m (ae_lo E) b -> AINV_A E m ->
    rw_cells bsegs m node [C8 (wz (ae_DOC E)); C8 (wz i)] -> rw_cells bsegs m (b + 72) [CB 8 oa; CB 8 ob; CB 4 oc; CB 4 od] ->
    bytes_at bsegs m Kp kb ->
    aevt RT PMc Σ1 K (MS (mkR (wz RA) (wz b) gp (wz TPV) t0 t1 t2 s0 (wz b) (wz (b + 72)) (wz node) (wz Kp) (wz Lk) a4 a5 a6 a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 (wz 2147450880) t3 t4 t5 t6) F (wz ATP_ATKEY_A) fc None m (seg_rom bsegs)).
  Proof using AF RC2 OK FDO MST LV TY NXT TILES I0 EN LOB BQ QN NB N8 B32 LKB KP0 KPL LK40 CKP KEYCL RA0 RA2 KF KN kb.
    intros until oc. intros ART0 MI0 ST0 AI0 NODE0 OUT0 KEY0.
    pose proof kc_facts as (FPW & HWlo & ARTW & AIW & SHZTg & SHZSg & SHZNg & SHZOg & EU).
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) (SB16 & NS8 & SN & SS & SL) PTRR P0' (D8 & DF & DL & DS & DT) LOW [HL HT]].
    pose proof (tiles_le _ (field_lt _ _ _ _ (elem_lt _ _ _ _ d)) _ _ _ TILES) as [IE CC].
    assert (TRN : forall my m2, ART RT Σ1 my -> munch W my m2 -> wmono bsegs my m2 ->
              rw_cells bsegs my node [C8 (wz (ae_DOC E)); C8 (wz i)] -> rw_cells bsegs m2 node [C8 (wz (ae_DOC E)); C8 (wz i)]).
    { intros my m2 HA MU WM ND. apply (rw_cells_agree_nw bsegs my m2 _ _ ND). apply (agree_of_munch _ _ _ _ MU).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. unfold W, atkey_W. cbn [outside]. clear - Hx BQ QN. lia. }
    assert (TRK : forall my m2, munch W my m2 -> bytes_at bsegs my Kp kb -> bytes_at bsegs m2 Kp kb).
    { intros my m2 MU KB. apply (bytes_at_transport bsegs W my m2 Kp kb KB MU). unfold W, atkey_W. cbn [disjoint_from fst snd]. rewrite LKB.
      pose proof LOW. unfold RT_STACK in LOB. clear - KP0 KPL LOB H. lia. }
    assert (TRA : forall my m2, ART RT Σ1 my -> agree_on PK m my -> munch W my m2 -> agree_on PK m m2).
    { intros my m2 HA AG MU. eapply agree_trans; [exact AG|]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. exact (PK_outside_W my x HA Hx). }
    pose proof (agree_refl PK m) as AG0.
    apply (aevt_evt RT AF PMc MST).
    eapply (atkey_pre E OK d _ m F fc i e c b (b + 72) node Kp Lk RA);
      [ exact TY| exact NXT| exact TILES| exact I0| exact EN| exact NODE0| lia| exact NB| exact N8| exact OUT0| lia| ul| clear - B32; Z.div_mod_to_equations; lia
      | pose proof LOW; ul| lia
      | intros m' MU WM; exact (AIW m m' AI0 MU WM)
      | intros m' MU WM; exact (shb_cells_of_art RT AF Σ1 m' (ARTW m m' ART0 MU WM))
      | intros m' MU WM; exact (lvl_shz_doc E OK m' (AIW m m' AI0 MU WM))
      | intros m' MU WM; exact (SHZTg m' (ARTW m m' ART0 MU WM))
      | intros m' MU WM; exact (SHZNg m' (ARTW m m' ART0 MU WM))
      | exact ST0| ul| ul| clear - B32; Z.div_mod_to_equations; lia| exact MI0| exact RA0| exact RA2| | ].
    -
      intros m1 y5 y6 y7 ya3 ya4 ya5 ya6 ya7 ys0 ys2 ys3 ys4 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 y31 j0 j16 j24 MU1 WM1 MI1 ST1 FR1 OUT1. apply evt_done.
      cbn [app] in FR1.
      lazymatch type of FR1 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
        pose proof (rw_cells_merge bsegs m1 (b + -144) [] [c0; c1; c2; c3; c4] rest FR1) as FR1' end.
      cbn [app cells_size csize Nat.add] in FR1'.
      eapply (atkey_nfK m1 F); [exact (ARTW m m1 ART0 MU1 WM1)| exact MI1| exact ST1| exact (AIW m m1 AI0 MU1 WM1)| exact (TRA m m1 ART0 AG0 MU1)
        | exact (TRN m m1 ART0 MU1 WM1 NODE0)| unfold atkey_saved; exact FR1'| exact OUT1].
    -
      intros m1 y1 y5 y6 y7 ya3 ya4 ya5 ya6 ya7 ys6 y28 y29 y30 y31 j0 NE MU1 WM1 MI1 ST1 FR1 OUT1. apply evt_done.
      eapply (atkey_loopK (S (Z.to_nat (e - i))) (i + 1) c m1 F); [exact TILES| exact NE| lia| lia
        | exact (ARTW m m1 ART0 MU1 WM1)| exact MI1| exact ST1| exact (AIW m m1 AI0 MU1 WM1)| exact (TRA m m1 ART0 AG0 MU1)
        | exact (TRN m m1 ART0 MU1 WM1 NODE0)| unfold atkey_frame; exact FR1| exact OUT1| exact (TRK m m1 MU1 KEY0)].
  Qed.
End ObjKC.
