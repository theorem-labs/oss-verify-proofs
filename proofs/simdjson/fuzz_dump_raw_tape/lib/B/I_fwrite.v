(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac ITree Nodes Decode SysStep ImageA RzCPS NodesA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim Monad Stdio Canon.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow X_bridge X_bridge2.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout R_small R_m2s I_consts RT_iface D_iface D_defs D_kit D_clx FX_Stdio_iface F_towrite F_fwrite I_readw2 I_read I_fwritew I_iodefs X_open.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Lemma lit_words : forall m, acc bsegs m LIT_BLK1 128 -> acc bsegs m LIT_BLK2 128 ->
  ro_cells bsegs m 0x7fffc388 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] /\ ro_cells bsegs m 0x7fffac60 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof.
  intros m H1 H2. unfold LIT_BLK1, LIT_BLK2 in *.
  pose proof (acc_word_zero m 0x21c40 ltac:(reflexivity) (acc_sub bsegs m _ _ 0x21c40 64 H1 ltac:(lia) ltac:(lia))) as W1.
  pose proof (acc_word_zero m 0x21c80 ltac:(reflexivity) (acc_sub bsegs m _ _ 0x21c80 64 H1 ltac:(lia) ltac:(lia))) as W2.
  pose proof (acc_word_zero m 0x16300 ltac:(reflexivity) (acc_sub bsegs m _ _ 0x16300 64 H2 ltac:(lia) ltac:(lia))) as W3.
  pose proof (acc_word_zero m 0x16340 ltac:(reflexivity) (acc_sub bsegs m _ _ 0x16340 64 H2 ltac:(lia) ltac:(lia))) as W4.
  change (shad 0x21c40) with 0x7fffc388 in W1. change (shad 0x21c80) with 0x7fffc390 in W2.
  change (shad 0x16300) with 0x7fffac60 in W3. change (shad 0x16340) with 0x7fffac68 in W4.
  destruct W1 as [_ B1]. destruct W2 as [_ B2]. destruct W3 as [_ B3]. destruct W4 as [_ B4].
  cbn [cells_bytes cbytes] in B1, B2, B3, B4 |- *. rewrite app_nil_r in B1, B2, B3, B4.
  split; (split; [cbn; tauto|]); cbn [cells_bytes cbytes]; rewrite app_nil_r.
  - apply bytes_at_app. split; [exact B1|]. rewrite length_le8. exact B2.
  - apply bytes_at_app. split; [exact B3|]. rewrite length_le8. exact B4.
Qed.

Lemma map_to_bytes_unsigned : forall (s : list byte), map (fun z => Z_to_bv 8 z) (map bv_unsigned s) = s.
Proof. intros s. rewrite map_map. erewrite map_ext; [apply map_id|]. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma Forall_unsigned_byte : forall (s : list byte), Forall (fun c => 0 <= c < 256) (map bv_unsigned s).
Proof.
  intros s. apply Forall_map. apply Forall_forall. intros b _. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

Lemma evw_to_bytes : forall fd (l : list Z), evw fd l = map (WriteEv (Z_to_bv 64 fd)) (to_bytes l).
Proof. intros fd l. unfold evw, to_bytes. rewrite map_map. reflexivity. Qed.

Section XFwrite.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis AF_ICPT : forall Σ m, ART RT Σ m -> icpt_consts m.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, STDERR_FILE in *; lia.

Theorem fwrite_ok : fwrite_stderr_icontract RT OUT_repA ERR_repA IO_FPA.
Proof using AF AF_ICPT.
  intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m sa s errp lo
    Ha0 Ha1 Ha2 Ha3 Herrp Hlen Hsa HB CHK HFD ERR0 (g & SG1 & SG2) ART0 MI0 CALL.
  subst a0 a1 a2 a3 errp.
  intros T c Hc Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as USR. unfold bv_modulus in USR. change (bv_unsigned sp) with usp in USR.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  rewrite ESP in Hc.
  destruct (AF_ICPT Σ m ART0) as (AI & RR & M2S & ACCP & RF & ACC1 & ACC2).
  destruct (lit_words m ACC1 ACC2) as (W1 & W2).
  assert (LO0 : 0x7fff7f800000 <= lo) by ul.
  set (len := Z.of_nat (length s)) in *.
  set (s' := map bv_unsigned s).
  assert (LS' : zlength s' = len) by (unfold zlength, s'; rewrite length_map; reflexivity).
  assert (SAR : 0x16300 <= sa /\ sa + len <= 0x21cc0) by (destruct Hsa as [->| ->]; lia).

  set (Qfin := fun (x : unit * unit) (ms' : machine_state) => exists (m3 : mem),
         (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
            ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7'
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m3 (seg_rom bsegs))
         /\ munch [(lo, usp); (0x173330, 0x173418)] m m3 /\ wmono bsegs m m3 /\ mem_inv bsegs m3 /\ stk bsegs m3 lo usp
         /\ stderr_wfile0 m3).
  assert (IMPL : impl bsegs (at_node bsegs) ((stderr_fwrite s' : @M unit unit) tt) (epost Qfin)
                   (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 sa) (Z_to_bv 64 len) (Z_to_bv 64 1)
                      (Z_to_bv 64 STDERR_FILE) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fwrite m)).
  { eapply impl_evt;
      [exact (fwrite_walkA usp sa len STDERR_FILE ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m lo ST LO0 ltac:(ul) ltac:(ul) ltac:(lia) ltac:(lia) ltac:(ul) RF AI MI0)|].
    intros ms1 (m1 & junk & -> & MU1 & WM1 & MI1 & FRb & FRt & ST1).
    assert (AG1 : agree_on (fun x => x < usp - 2144) m m1).
    { apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn. split; [lia| exact I]. }
    assert (ERR1 : stderr_wfile0 m1).
    { apply (stderr_wfile0_agree m m1); [| exact WM1| exact ERR0]. apply (agree_sub _ _ _ _ AG1). intros x Hx. ul. }
    assert (HB1 : bytes_at bsegs m1 (bv_unsigned (Z_to_bv 64 sa)) (map (fun z => Z_to_bv 8 z) s')).
    { rewrite unsigned_lit by lia. unfold s'. rewrite map_to_bytes_unsigned.
      apply (bytes_at_agree bsegs m m1 _ _ HB). apply (agree_sub _ _ _ _ AG1). intros x Hx. fold len in Hx. ul. }
    assert (SSP1 : ssp_cells m1 g).
    { split.
      - apply (ro_cells_agree bsegs m m1 _ _ SG1). apply (agree_sub _ _ _ _ AG1). intros x Hx. cbn in Hx. ul.
      - apply (ro_cells_agree bsegs m m1 _ _ SG2). apply (agree_sub _ _ _ _ AG1). intros x Hx. cbn in Hx. ul. }
    assert (EU1 : bv_unsigned (Z_to_bv 64 (usp + -2128)) = usp + -2128) by (apply unsigned_lit; ul).
    pose proof (@fwrite_diag_proof unit towrite_proof (Z_to_bv 64 0x6ca40) (Z_to_bv 64 (usp + -2128)) gp tp t0 t1 t2
                  (Z_to_bv 64 usp) (Z_to_bv 64 len) (Z_to_bv 64 sa) (Z_to_bv 64 len) (Z_to_bv 64 1) (Z_to_bv 64 STDERR_FILE)
                  (Z_to_bv 64 0x158210) a5 a6 a7 (Z_to_bv 64 sa) (Z_to_bv 64 STDERR_FILE) (Z_to_bv 64 1) (Z_to_bv 64 1)
                  s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 tt lo g s' ERR1 HB1 (Forall_unsigned_byte s) ltac:(rewrite LS'; lia)
                  ltac:(rewrite LS'; reflexivity) eq_refl eq_refl ltac:(rewrite EU1; exact ST1) ltac:(rewrite EU1; unfold FWRITE_DEPTH; ul)
                  ltac:(unfold GLOBALS_TOP; ul) ltac:(rewrite unsigned_lit by lia; rewrite LS'; left; ul)
                  ltac:(rewrite unsigned_lit by lia; rewrite LS'; left; ul) SSP1 MI1) as IM.
    unfold implM in IM.
    eapply impl_post_evt''; [exact IM|].
    intros [|[xr st']] ms2 H2; [apply evt_done; exact I|].
    cbn [epost fst snd] in H2 |- *.
    destruct H2 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2
                    & ST2 & ERR2 & SSP2 & _).
    rewrite EU1 in MU2, ST2.
    rewrite (ret_pc_even 0x6ca40) by lia.
    assert (AG2 : agree_on (fun x => usp - 2128 <= x \/ ((0x16e770 <= x < 0x16e790) \/ (0x177bb8 <= x < 0x177bc0) \/ (0x1788a0 <= x < 0x1788b8)) \/ (SHB <= x < 0x10007fff8000)) m1 m2).
    { apply (agree_of_munch _ _ _ _ MU2). intros x Hx. cbn. unfold SHB in Hx. split; [lia|]. split; [ul| exact I]. }
    pose proof (rw_cells_agree bsegs m1 m2 _ _ FRb ltac:(apply (agree_sub _ _ _ _ AG2); intros x Hx; cbn in Hx; left; lia) WM2) as FRb2.
    pose proof (rw_cells_agree bsegs m1 m2 _ _ FRt ltac:(apply (agree_sub _ _ _ _ AG2); intros x Hx; cbn in Hx; left; lia) WM2) as FRt2.
    assert (AG12 : agree_on (fun x => ((0x16e770 <= x < 0x16e790) \/ (0x177bb8 <= x < 0x177bc0) \/ (0x1788a0 <= x < 0x1788b8)) \/ (SHB <= x < 0x10007fff8000)) m m2).
    { apply (agree_trans _ m m1 m2); [apply (agree_sub _ _ _ _ AG1); intros x Hx; unfold SHB in Hx; ul|].
      apply (agree_sub _ _ _ _ AG2). intros x Hx. right. exact Hx. }
    assert (M2S2 : m2s_cells m2).
    { destruct M2S as (G1 & G2 & G3). split; [| split].
      - apply (rw_cells_agree bsegs m m2 _ _ G1); [| exact (wmono_trans bsegs m m1 m2 WM1 WM2)].
        apply (agree_sub _ _ _ _ AG12). intros x Hx. cbn in Hx. lia.
      - apply (rw_cells_agree bsegs m m2 _ _ G2); [| exact (wmono_trans bsegs m m1 m2 WM1 WM2)].
        apply (agree_sub _ _ _ _ AG12). intros x Hx. cbn in Hx. lia.
      - apply (rw_cells_agree bsegs m m2 _ _ G3); [| exact (wmono_trans bsegs m m1 m2 WM1 WM2)].
        apply (agree_sub _ _ _ _ AG12). intros x Hx. cbn in Hx. lia. }
    assert (W1' : ro_cells bsegs m2 0x7fffc388 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
    { apply (ro_cells_agree bsegs m m2 _ _ W1). apply (agree_sub _ _ _ _ AG12). intros x Hx. cbn in Hx. unfold SHB. lia. }
    assert (W2' : ro_cells bsegs m2 0x7fffac60 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
    { apply (ro_cells_agree bsegs m m2 _ _ W2). apply (agree_sub _ _ _ _ AG12). intros x Hx. cbn in Hx. unfold SHB. lia. }
    eapply evt_mono.
    { apply (fwrite_walkB usp sa len STDERR_FILE ra gp tp t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3' t4' t5' t6' F fc m2 lo junk ST2 LO0 ltac:(ul) ltac:(ul) Hsa ltac:(lia) ltac:(ul) M2S2 W2' W1' FRb2 FRt2 MI2). }
    intros ms3 (RS3 & ST3). exists m2. split; [exact RS3|].
    split.
    { apply (munch_merge [(usp - 2144, usp)] [(lo, usp + -2128); (0x173330, 0x173330 + 232)] _ m m1 m2 MU1 MU2).
      intros x Hx. cbn in Hx |- *. unfold RT_STACK in *. intuition lia. }
    split; [exact (wmono_trans bsegs m m1 m2 WM1 WM2)|]. split; [exact MI2|]. split; [exact ST3| exact ERR2]. }

  assert (TOK : tok [2] ((stderr_fwrite s' : @M unit unit) tt)).
  { unfold stderr_fwrite. rewrite LS'. replace (0 <? len) with true by (symmetry; apply Z.ltb_lt; lia).
    unfold stdio_writev. apply tok_wv_loop; [left; reflexivity| cbn; lia| |];
      unfold WV_FUEL, iov_start, iov_total; cbn [concat]; rewrite app_nil_r; rewrite LS'; lia. }
  assert (RZ : realizes bsegs c (TT ((stderr_fwrite s' : @M unit unit) tt) (fun _ => t_emit [] T))).
  { apply (impl_realizes bsegs SEGTOP_A asegs_wx asegs_below [2] _ (rt_allow RT Σ) (fun mo => ARTM RT Σ mo /\ PMfd F0 fs0 mo) Qfin
             (fun _ => t_emit [] T)
             (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 sa) (Z_to_bv 64 len) (Z_to_bv 64 1)
                (Z_to_bv 64 STDERR_FILE) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fwrite m) c
             (ASTA_PM_mat_stable RT AF Σ F0 fs0)); [| exact TOK| exact Hc| exact IMPL|].
    - intros mo fd (HAR & HF & _) Hin. cbn in Hin. destruct Hin as [<-|[]]. rewrite HF. exact HFD.
    - intros x ms' c' HQ Hc'.
      assert (R : realizes bsegs c' T).
      { apply Hk. eapply ASTA_conseq; [exact Hc'|]. intros ms <-.
        destruct HQ as (m3 & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->) & MU3 & WM3 & MI3
                        & ST3 & ERR3).
        exists (Z_to_bv 64 1), m3. split.
        { rewrite ESP. do 16 eexists. reflexivity. }
        split; [split; [| split; [exact MI3| split; [exact WM3| exact ST3]]]|].
        - apply (af_frame RT AF Σ m m3 lo ART0); [ul| | exact WM3].
          intros a Ha. apply MU3. cbn. split; [intros Hin; apply Ha; left; ul|]. split; [| exact I].
          intros Hin. apply Ha. right; left. apply client_static_intro. lia.
        - split; [| split; [exact ERR3|]].
          + intros a Ha Hout. apply MU3. cbn in Hout |- *. destruct Hout as (O1 & O2 & O3 & _). split; [| split; [exact O1| exact I]].
            destruct (aclient_split RT AF Σ m usp _ ART0 Ha); ul.
          + intros so0 OUT. apply (stdout_file_agree so0 m m3); [| exact WM3| exact OUT].
            apply (agree_of_munch _ _ _ _ MU3). intros y Hy. cbn. split; [ul| split; [lia| exact I]]. }
      eapply rz_conseq; [exact R|]. apply t_eq_sym, t_emit_nil_eq. exact (realizes_nonempty bsegs _ _ R). }
  eapply rz_conseq; [exact RZ|].
  unfold stderr_fwrite. rewrite LS'. replace (0 <? len) with true by (symmetry; apply Z.ltb_lt; lia).
  unfold stdio_writev.
  eapply t_eq_trans.
  { apply (TT_wv_loop (WV_FUEL (iov_start [] s')) 2 (iov_start [] s') tt (fun _ => t_emit [] T)); [cbn; lia| | | apply t_emit_has_nil];
      unfold WV_FUEL, iov_start, iov_total; cbn [concat]; rewrite app_nil_r; rewrite LS'; lia. }
  cbn [iov_start concat]. rewrite app_nil_r. rewrite <- evw_to_bytes.
  eapply t_eq_trans; [apply t_eq_sym, t_emit_app|]. rewrite app_nil_r. apply t_eq_refl.
Qed.

End XFwrite.
