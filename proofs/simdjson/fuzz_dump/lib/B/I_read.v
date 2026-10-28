(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac ImageA Nodes RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout R_small R_m2s R_thread I_consts RT_iface D_iface D_defs D_kit D_clx D_rlkit X_open I_readw I_readw2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Lemma nretA_MSsvc_w : forall R F pc x8 fc rv m ro r ws,
  nretA (MSsvc R F pc x8 fc rv m ro) (mkEffect r ws []) = MS (bvmap_set 10 r R) F (pc + Z_to_bv 64 4)%bv fc rv
    (apply_writes (apply_zeros (apply_unmaps m []) []) ws) ro.
Proof. reflexivity. Qed.

Lemma acc_agree_sh : forall m m' a n, acc bsegs m a n -> 0 <= a -> a + n <= USTACK_TOP ->
  agree_on (fun x => SHB <= x < 0x10007fff8000) m m' -> acc bsegs m' a n.
Proof.
  intros m m' a n H Ha Hn AG i Hi. destruct (H i Hi) as (b & Hb & Hok). exists b. split; [| exact Hok].
  apply (bytes_at_agree bsegs m m' _ _ Hb). apply (agree_sub _ _ m m' AG). intros x Hx. cbn [length] in Hx.
  unfold shad, SHB, USTACK_TOP in *. split; [| Z.div_mod_to_equations]; lia.
Qed.

Lemma acc_app : forall m a n k, acc bsegs m a n -> acc bsegs m (a + n) k -> 0 <= n -> acc bsegs m a (n + k).
Proof.
  intros m a n k H1 H2 Hn i Hi. destruct (Z_lt_dec i n) as [L|L]; [apply H1; lia|].
  replace (a + i) with (a + n + (i - n)) by lia. apply H2. lia.
Qed.

Lemma stage_words : forall m, acc bsegs m RS_PAD 16 -> acc bsegs m g_read_stage 112 ->
  ro_cells bsegs m 0x800CB2F0 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof.
  intros m H1 H2. unfold RS_PAD, g_read_stage in *.
  pose proof (acc_app m 6920064 16 112 H1 H2 ltac:(lia)) as H.
  pose proof (acc_word_zero m 6920064 ltac:(reflexivity) (acc_sub bsegs m _ _ 6920064 64 H ltac:(lia) ltac:(lia))) as W1.
  pose proof (acc_word_zero m 6920128 ltac:(reflexivity) (acc_sub bsegs m _ _ 6920128 64 H ltac:(lia) ltac:(lia))) as W2.
  change (shad 6920064) with 2148315888 in W1. change (shad 6920128) with 2148315896 in W2.
  destruct W1 as [_ B1]. destruct W2 as [_ B2]. split; [cbn; tauto|].
  cbn [cells_bytes cbytes] in B1, B2 |- *. rewrite app_nil_r in B1, B2 |- *.
  apply bytes_at_app. split; [exact B1|]. rewrite length_le8. exact B2.
Qed.

Section XRead.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis AF_ICPT : forall Σ m, ART RT Σ m -> icpt_consts m.
Hypothesis RIP : rip_stmt.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, g_read_stage in *; lia.

Lemma aclient_split : forall Σ m usp a, ART RT Σ m -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp a ->
  usp <= a \/ a < rt_sp0 RT Σ - STACK_WIN.
Proof using AF.
  intros Σ m usp a ART0 [H|[H|[H|[H|H]]]].
  - left; lia.
  - right. pose proof (client_static_range a H). pose proof (af_sp0_range RT AF Σ m ART0). ul.
  - right. destruct H as (p & n & Hin & Hp). pose proof (af_live_range RT AF Σ m p n ART0 Hin). lia.
  - right. destruct H as (f & k & Hin & Hf). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & H2 & _).
    unfold fs_size in *. pose proof (Z.shiftl_nonneg 64 (Z.of_nat k)) as E. lia.
  - right. destruct H as (f & k & Hin & Hf). pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & H2 & _).
    pose proof (af_sp0_range RT AF Σ m ART0). pose proof (af_sp0_win RT AF Σ m ART0).
    unfold shad, SHB in Hf. unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *. Z.div_mod_to_equations. lia.
Qed.

Theorem read_file_ok : read_icontract_file RT.
Proof using AF AF_ICPT RIP.
  intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    fd buf count p off data lo Ha0 Ha1 Ha2 HBUF Hfd Hcnt Hb0 Hbt CHK HLK HFS ART0 MI0 CALL bs.
  subst a0 a1 a2 buf.
  intros T c Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as USR. unfold bv_modulus in USR. change (bv_unsigned sp) with usp in USR.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  rewrite ESP in Hc.
  destruct (AF_ICPT Σ m ART0) as (AI & RR & M2S & ACCP & _).
  destruct CHK as (CHKa & CHKcl & CHKwr). destruct (CHKa ltac:(lia)) as (ACCB & _).
  assert (ACC112 : acc bsegs m g_read_stage 112).
  { apply (af_acc_static RT AF Σ m _ 112 ART0); [ul|]. intros i Hi. split; [apply stage_static; lia| unfold g_read_stage; lia]. }
  pose proof (stage_words m ACCP ACC112) as SW.
  assert (LO0 : 0x7fff7f800000 <= lo) by ul.
  pose proof (read_walkA usp fd count ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST LO0 ltac:(ul) ltac:(ul) ltac:(lia) ltac:(lia) RR AI MI0) as W1.
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ c (asta_evt RT AF Σ F0 fs0 _ _ W1') Hc). intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & junk & junk1 & -> & MU1 & WM1 & MI1 & FRb & FRt & FRr & ST1) & Hc1').
  set (msA := MSsvc (mkR (Z_to_bv 64 0x1672b0) (Z_to_bv 64 (usp + -2144)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 g_read_stage)
                       (Z_to_bv 64 fd) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 count) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                       (Z_to_bv 64 0) (Z_to_bv 64 63) (Z_to_bv 64 count) (Z_to_bv 64 fd) (Z_to_bv 64 1) s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x16185c) (Z_to_bv 64 63) fc None m1 (seg_rom bsegs)) in *.
  assert (WR1 : wr_at bsegs m1 g_read_stage count) by exact (wr_at_transport bsegs m m1 _ _ CHKwr WM1).
  unfold ASTA in Hc1'.
  apply (ast_read_file bsegs SEGTOP_A asegs_wx asegs_below (rt_allow RT Σ) (eq msA) (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo)
           (fun ms => nretA msA (mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 g_read_stage) bs) []) = ms)
           (fun mo => ARTM RT Σ mo /\ PMfd (fd_insert F0 (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) fs0 mo)
           fd g_read_stage count p off data); [lia| lia| ul| exact (ASTA_PM_mat_stable RT AF Σ _ fs0)| | | exact Hc1'|].
  - intros ms <-. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact WR1| reflexivity].
  - intros mo (HAR & HF & HF2). rewrite HF, HF2. split; [exact HLK|]. split; [exact HFS|].
    split; [apply (af_with_fds RT AF); exact HAR| split; [reflexivity| exact HF2]].
  - intros c2 Hc2.
    set (r := Z.of_nat (length bs)) in *.
    assert (Hr : 0 <= r <= count).
    { subst r bs. rewrite file_read_unguarded, length_firstn. unfold word_to_nat. rewrite unsigned_lit by lia. lia. }
    set (m2 := write_to_mem m1 (wa g_read_stage) bs).
    assert (EQ : nretA msA (mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 g_read_stage) bs) [])
                 = MS (mkR (Z_to_bv 64 0x1672b0) (Z_to_bv 64 (usp + -2144)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 g_read_stage)
                        (Z_to_bv 64 r) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 count) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                        (Z_to_bv 64 0) (Z_to_bv 64 63) (Z_to_bv 64 count) (Z_to_bv 64 fd) (Z_to_bv 64 1) s5 s6 s7 s8 s9 s10 s11
                        t3 t4 t5 t6)
                   F (Z_to_bv 64 0x161860) fc None m2 (seg_rom bsegs)).
    { unfold msA. rewrite nretA_MSsvc_w, mkR_set_a0, pc_93368, apply_mem_delivered. reflexivity. }
    rewrite EQ in Hc2. clear EQ.

    assert (BS2 : bytes_at bsegs m2 g_read_stage bs) by (apply bytes_at_write_same; ul).
    assert (MU2 : munch [(g_read_stage, g_read_stage + r)] m1 m2).
    { apply munch_write; [apply munch_refl| ul| ul|]. unfold inside. cbn. lia. }
    assert (WM2 : wmono bsegs m1 m2) by (apply wmono_write, wmono_refl).
    assert (MI2 : mem_inv bsegs m2).
    { apply mem_inv_store; [exact MI1|]. rewrite <- (Z.add_0_r g_read_stage). apply (wr_at_store_ok bsegs m1 _ count 0 _ WR1); lia. }

    assert (MU12 : munch [(usp - 2144, usp); (g_read_stage, g_read_stage + r)] m m2).
    { apply (munch_merge [(usp - 2144, usp)] [(g_read_stage, g_read_stage + r)] _ m m1 m2 MU1 MU2).
      intros x Hx. cbn in Hx |- *. intuition lia. }
    assert (WM12 : wmono bsegs m m2) by exact (wmono_trans bsegs m m1 m2 WM1 WM2).

    assert (FIN : forall c3 m3 (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ASTA RT Σ (PMfd (fd_insert F0 (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) fs0)
        (eq (MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m3 (seg_rom bsegs))) c3 ->
      munch [(usp + -2208, usp)] m2 m3 -> wmono bsegs m2 m3 -> mem_inv bsegs m3 -> stk bsegs m3 lo usp ->
      realizes bsegs c3 T).
    { intros c3 m3 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Hc3 MU3 WM3 MI3 ST3. apply Hk.
      assert (MUT : munch [(usp - 2208, usp); (g_read_stage, g_read_stage + r)] m m3).
      { apply (munch_merge _ [(usp + -2208, usp)] _ m m2 m3 MU12 MU3). intros x Hx. cbn in Hx |- *. intuition lia. }
      eapply ASTA_conseq; [exact Hc3|]. intros ms <-. exists m3. split.
      { rewrite ESP. do 15 eexists. reflexivity. }
      split; [split; [| split; [exact MI3| split; [exact (wmono_trans bsegs m m2 m3 WM12 WM3)| exact ST3]]]|].
      - apply (af_frame RT AF Σ m m3 (usp - 2304) ART0); [ul| | exact (wmono_trans bsegs m m2 m3 WM12 WM3)].
        intros a Ha. apply MUT. cbn. split; [intros Hin; apply Ha; left; ul|]. split; [| exact I].
        intros Hin. apply Ha. right; left. apply stage_static'. lia.
      - split.
        + intros a Ha Hout. apply MUT. cbn in Hout |- *. split; [| exact Hout].
          destruct (aclient_split Σ m usp _ ART0 Ha); ul.
        + apply (bytes_at_agree bsegs m2 m3 _ _ BS2). apply (agree_of_munch _ _ _ _ MU3). intros x Hx. cbn. ul. }

    assert (AG2 : agree_on (fun x => usp - 2144 <= x < usp) m1 m2) by (apply (agree_of_munch _ _ _ _ MU2); intros x Hx; cbn; ul).
    assert (AGS : agree_on (fun x => 0x16e1d0 <= x < 0x177e38 \/ SHB <= x < 0x10007fff8000) m m2).
    { apply (agree_of_munch _ _ _ _ MU12). intros x Hx. cbn. unfold SHB in Hx. split; [ul| split; [| exact I]]. ul. }
    pose proof (rw_cells_agree bsegs m1 m2 _ _ FRr ltac:(apply (agree_sub _ _ _ _ AG2); intros x Hx; cbn in Hx; lia) WM2) as FRr2.
    pose proof (rw_cells_agree bsegs m1 m2 _ _ FRb ltac:(apply (agree_sub _ _ _ _ AG2); intros x Hx; cbn in Hx; lia) WM2) as FRb2.
    pose proof (rw_cells_agree bsegs m1 m2 _ _ FRt ltac:(apply (agree_sub _ _ _ _ AG2); intros x Hx; cbn in Hx; lia) WM2) as FRt2.
    assert (ST2 : stk bsegs m2 lo (usp + -2144)) by (apply stk_write; [exact ST1| ul| ul]).
    assert (M2S2 : m2s_cells m2).
    { destruct M2S as (G1 & G2 & G3). split; [| split].
      - apply (rw_cells_agree bsegs m m2 _ _ G1); [| exact WM12]. apply (agree_sub _ _ _ _ AGS). intros x Hx. cbn in Hx. lia.
      - apply (rw_cells_agree bsegs m m2 _ _ G2); [| exact WM12]. apply (agree_sub _ _ _ _ AGS). intros x Hx. cbn in Hx. lia.
      - apply (rw_cells_agree bsegs m m2 _ _ G3); [| exact WM12]. apply (agree_sub _ _ _ _ AGS). intros x Hx. cbn in Hx. lia. }
    assert (SW2 : ro_cells bsegs m2 0x800CB2F0 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
    { apply (ro_cells_agree bsegs m m2 _ _ SW). apply (agree_sub _ _ _ _ AGS). intros x Hx. cbn in Hx. unfold SHB. lia. }
    destruct (Z.eq_dec r 0) as [R0|R0]; [|destruct (Z_le_gt_dec r 64) as [R64|R64]].
    +
      rewrite R0 in Hc2.
      pose proof (read_walkB_eof usp fd count ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 lo junk junk1
                    ST2 LO0 ltac:(ul) ltac:(ul) ltac:(lia) ltac:(lia) FRr2 FRb2 FRt2 MI2) as W2.
      lazymatch type of W2 with evt bsegs _ ?X =>
        assert (W2' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W2) end.
      clear W2.
      apply (cps_realizes bsegs _ _ _ c2 (asta_evt RT AF Σ _ fs0 _ _ W2') Hc2). intros c3 Hc3.
      destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & ((t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->) & ST3) & Hc3').
      rewrite <- R0 in Hc3'.
      exact (FIN c3 m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Hc3' (munch_refl _ _) (wmono_refl bsegs _) MI2 ST3).
    +
      pose proof (read_walkB_qc usp fd count r ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 lo junk junk1
                    ST2 LO0 ltac:(ul) ltac:(ul) ltac:(lia) ltac:(lia) ltac:(lia) M2S2 SW2 FRr2 FRb2 FRt2 MI2) as W2.
      lazymatch type of W2 with evt bsegs _ ?X =>
        assert (W2' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W2) end.
      clear W2.
      apply (cps_realizes bsegs _ _ _ c2 (asta_evt RT AF Σ _ fs0 _ _ W2') Hc2). intros c3 Hc3.
      destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & ((t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->) & ST3) & Hc3').
      exact (FIN c3 m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Hc3' (munch_refl _ _) (wmono_refl bsegs _) MI2 ST3).
    +
      assert (ACC2 : acc bsegs m2 g_read_stage r).
      { apply (acc_agree_sh m m2); [apply (acc_sub bsegs m _ _ g_read_stage r ACCB); lia| ul| ul|].
        apply (agree_sub _ _ _ _ AGS). intros x Hx. right. exact Hx. }
      pose proof (read_walkB_rip RIP usp fd count r ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 lo junk junk1
                    ST2 LO0 ltac:(ul) ltac:(ul) ltac:(lia) ltac:(lia) ltac:(lia) M2S2 ACC2 FRr2 FRb2 FRt2 MI2) as W2.
      lazymatch type of W2 with evt bsegs _ ?X =>
        assert (W2' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W2) end.
      clear W2.
      apply (cps_realizes bsegs _ _ _ c2 (asta_evt RT AF Σ _ fs0 _ _ W2') Hc2). intros c3 Hc3.
      destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (m3 & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->) & MU3 & WM3 & MI3 & ST3) & Hc3').
      exact (FIN c3 m3 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Hc3' MU3 WM3 MI3 ST3).
Qed.

Theorem read_dir_ok : read_icontract_dir RT.
Proof using AF AF_ICPT.
  intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    fd buf count lo Ha0 Ha1 Ha2 HBUF Hfd Hcnt Hb0 Hbt CHK HLK HERRS HTP (errv & ERR0) ART0 MI0 CALL.
  subst a0 a1 a2 buf tp.
  intros T c Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as USR. unfold bv_modulus in USR. change (bv_unsigned sp) with usp in USR.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  rewrite ESP in Hc.
  destruct (AF_ICPT Σ m ART0) as (AI & RR & M2S & ACCP & _).
  destruct CHK as (CHKa & CHKcl & CHKwr).
  assert (EE : errno_cell (Z_to_bv 64 0x6ab368) = 0x6ab2c4) by (unfold errno_cell; rewrite unsigned_lit by lia; reflexivity).
  rewrite EE in ERR0, HERRS, Hk.
  assert (LO0 : 0x7fff7f800000 <= lo) by ul.
  pose proof (read_walkA usp fd count ra gp (Z_to_bv 64 0x6ab368) t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m lo ST LO0 ltac:(ul) ltac:(ul) ltac:(lia) ltac:(lia) RR AI MI0) as W1.
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ c (asta_evt RT AF Σ F0 fs0 _ _ W1') Hc). intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & junk & junk1 & -> & MU1 & WM1 & MI1 & FRb & FRt & FRr & ST1) & Hc1').
  set (msA := MSsvc (mkR (Z_to_bv 64 0x1672b0) (Z_to_bv 64 (usp + -2144)) gp (Z_to_bv 64 0x6ab368) t0 t1 t2 (Z_to_bv 64 usp)
                       (Z_to_bv 64 g_read_stage) (Z_to_bv 64 fd) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 count) (Z_to_bv 64 0)
                       (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 63) (Z_to_bv 64 count) (Z_to_bv 64 fd) (Z_to_bv 64 1)
                       s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x16185c) (Z_to_bv 64 63) fc None m1 (seg_rom bsegs)) in *.
  unfold ASTA in Hc1'.
  apply (ast_read_dir bsegs SEGTOP_A asegs_wx asegs_below (rt_allow RT Σ) (eq msA) (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo)
           (fun ms => nretA msA (efferr EISDIR) = ms) (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo)
           fd g_read_stage count); [lia| lia| ul| ul| exact (ASTA_PM_mat_stable RT AF Σ _ fs0)| | | exact Hc1'|].
  - intros ms <-. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
  - intros mo (HAR & HF & HF2). rewrite HF. split; [exact HLK|]. split; [exact HAR| split; assumption].
  - intros c2 Hc2.
    assert (EQ : nretA msA (efferr EISDIR)
                 = MS (mkR (Z_to_bv 64 0x1672b0) (Z_to_bv 64 (usp + -2144)) gp (Z_to_bv 64 0x6ab368) t0 t1 t2 (Z_to_bv 64 usp)
                        (Z_to_bv 64 g_read_stage) (Z_to_bv 64 (- 21)) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 count) (Z_to_bv 64 0)
                        (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 63) (Z_to_bv 64 count) (Z_to_bv 64 fd) (Z_to_bv 64 1)
                        s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x161860) fc None m1 (seg_rom bsegs)).
    { unfold msA, efferr, eff0, errno_ret. rewrite nretA_MSsvc, mkR_set_a0, pc_93368. reflexivity. }
    rewrite EQ in Hc2. clear EQ.
    assert (ERR1 : rw_cells bsegs m1 0x6ab2c4 [C4 errv]).
    { apply (rw_cells_agree bsegs m m1 _ _ ERR0); [| exact WM1].
      apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn in Hx |- *. split; [ul| exact I]. }
    pose proof (read_walkB_err usp fd count 21 ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo junk junk1 errv
                  ST1 LO0 ltac:(ul) ltac:(ul) ltac:(lia) ltac:(lia) ltac:(lia) ERR1 FRr FRb FRt MI1) as W2.
    lazymatch type of W2 with evt bsegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes bsegs _ _ _ c2 (asta_evt RT AF Σ _ fs0 _ _ W2') Hc2). intros c3 Hc3. apply Hk.
    destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (m3 & RS & MU3 & WM3 & MI3 & ERR3 & ST3) & Hc3').
    assert (MUT : munch [(usp - 2144, usp); (0x6ab2c4, 0x6ab2c8)] m m3).
    { apply (munch_merge [(usp - 2144, usp)] [(usp + -2144, usp); (0x6ab2c4, 0x6ab2c8)] _ m m1 m3 MU1 MU3).
      intros x Hx. cbn in Hx |- *. intuition lia. }
    assert (WMT : wmono bsegs m m3) by exact (wmono_trans bsegs m m1 m3 WM1 WM3).
    eapply ASTA_conseq; [exact Hc3'|]. intros ms <-. exists m3. split.
    { rewrite ESP. destruct RS as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->).
      do 15 eexists. reflexivity. }
    split; [split; [| split; [exact MI3| split; [exact WMT| exact ST3]]]|].
    + apply (af_frame RT AF Σ m m3 (usp - 2304) ART0); [ul| | exact WMT].
      intros a Ha. apply MUT. cbn. split; [intros Hin; apply Ha; left; ul|]. split; [| exact I].
      intros Hin. apply Ha. right; left. replace (bv_unsigned a) with (0x6ab2c4 + (bv_unsigned a - 0x6ab2c4)) by lia.
      apply HERRS. lia.
    + intros a Ha Hout. apply MUT. cbn in Hout |- *. split; [| exact Hout].
      destruct (aclient_split Σ m usp _ ART0 Ha); ul.
Qed.

End XRead.
