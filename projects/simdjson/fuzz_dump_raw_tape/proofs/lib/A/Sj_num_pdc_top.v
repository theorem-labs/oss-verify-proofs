(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_abig Sj_num_acall Sj_num_pdc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section PDTOP.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RTF : rt_contracts_f RT.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.
  Hypothesis HP5 : p5a_stmt RT PMc.

  Variables (Σ0 : rts RT) (K : config -> Prop).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (X lo cr0 : Z) (me : mem).
  Notation SP := (bv_unsigned sp).
  Hypothesis ETP : tp = Z_to_bv 64 0x6a0068.
  Hypothesis ROOM : (lo + PDCA_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis LOR : (rt_sp0 RT Σ0 - STACK_WIN <= lo)%Z.
  Hypothesis FRL : (length (rt_frames RT Σ0) < FRAMES_MAX)%nat.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis XFR : exists f c, In (f, c) (rt_frames RT Σ0) /\ (f <= X)%Z /\ (X + 504 <= f + fs_size c - 8)%Z.
  Hypothesis XNUM : (0x6c2000 <= X /\ X + 504 <= lo
                     /\ (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)
                     /\ 0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo)%Z.
  Hypothesis CR0 : (cr0 <= rt_credit RT Σ0)%Z.
  Hypothesis HK : forall (Σ' : rts RT) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m', frm0 fc' ->
     rt_after RT Σ' SP lo me m' -> rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) SP [(X, X + 504)%Z] me m' ->
     abig RT Σ' m' X ->
     rt_frames RT Σ' = rt_frames RT Σ0 -> rt_live RT Σ' = rt_live RT Σ0 -> rt_sp0 RT Σ' = rt_sp0 RT Σ0 ->
     (rt_credit RT Σ0 - cr0 <= rt_credit RT Σ')%Z ->
     aevt RT PMc Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F' (ret_pc ra) fc' None m' (seg_rom asegs)).
  Collection PDH := ETP ROOM TOP SP16 LOR FRL X8 XFR XNUM CR0.

  Definition pd_srel (Σ : rts RT) (used : Z) : Prop :=
    rt_frames RT Σ = rt_frames RT Σ0 /\ rt_live RT Σ = rt_live RT Σ0 /\ rt_sp0 RT Σ = rt_sp0 RT Σ0 /\ (rt_credit RT Σ0 - used <= rt_credit RT Σ)%Z.
  Definition pd_mrel (mm : mem) : Prop :=
    wmono asegs me mm /\ rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) SP [(X, X + 504)%Z] me mm.
  Notation W := [(SP - 64, SP); (X, X + 504)]%Z.

  Lemma pd_fpok : forall Σ used, pd_srel Σ used -> fp_ok RT Σ lo W.
  Proof using PDH.
    intros Σ used (EF & _). unfold PDCA_STACK, P5A_STACK, LMA_STACK, RT_STACK in ROOM.
    constructor; [left; cbn [fst snd]; lia|]. constructor; [| constructor].
    right; right; left. destruct XFR as (f & c & Hin & F1 & F2). exists f, c. rewrite EF. cbn [fst snd]. split; [exact Hin| lia].
  Qed.

  Lemma pd_mrel_step : forall Σ used mb mm, pd_srel Σ used -> ART RT Σ mb -> pd_mrel mb -> munch W mb mm -> wmono asegs mb mm -> pd_mrel mm.
  Proof using AF PDH.
    intros Σ used mb mm (EF & EL & ES & _) HA [WM0 PR0] MU WM. split; [exact (wmono_trans asegs _ _ _ WM0 WM)|].
    eapply pres_fp_trans; [exact PR0|]. apply (pres_fp_of_munch _ _ _ _ W _ _ MU).
    intros a Ha Hd. rewrite <- EL, <- EF in Ha. pose proof (aclient_split_c RT AF Σ mb _ a HA Ha) as SPL. rewrite ES in SPL.
    unfold PDCA_STACK, P5A_STACK, LMA_STACK, RT_STACK in ROOM. cbn [outside] in Hd |- *. destruct Hd as [Hd _].
    split; [lia|]. split; [exact Hd| exact I].
  Qed.

  Lemma pd_mrel_ex : forall Σ used mb m' d n, pd_srel Σ used -> pd_mrel mb -> wmono asegs mb m' ->
    rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (SP + -64) d n mb m' -> (X <= d)%Z -> (d + n <= X + 504)%Z -> pd_mrel m'.
  Proof using PDH.
    intros Σ used mb m' d n (EF & EL & _) [WM0 PR0] WM PR D1 D2. split; [exact (wmono_trans asegs _ _ _ WM0 WM)|].
    eapply pres_fp_trans; [exact PR0|]. rewrite EL, EF in PR. intros a Ha Hd. apply PR.
    - eapply aclient_mono; [exact Ha| auto| auto| lia].
    - cbn [outside] in Hd. lia.
  Qed.

  Lemma pd_exit : forall Σ used F fc mb, pd_srel Σ used -> (used <= cr0)%Z -> frm0 fc -> ART RT Σ mb -> pd_mrel mb ->
    pd_exit_k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo mb (fun ms' => aevt RT PMc Σ K ms').
  Proof using AF PDH HK.
    intros Σ used F fc mb SR HU FRM HA MR. unfold pd_exit_k. intros until len. intros INV.
    destruct INV as ((j0 & FR) & (bs & XA & XL) & XN & LEN & ZR & MI & MU & WM & ST).
    pose proof SR as (EF & EL & ES & EC).
    destruct XNUM as (XN0 & XN1 & XN2 & XN3 & XN4).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold PDCA_STACK, P5A_STACK, LMA_STACK, RT_STACK, USTACK_TOP in ROOM, TOP.
    pose proof (repeat_length (Z_to_bv 8 0) 63) as RL.
    do 8 zstep. release_frame FR ST (bv_unsigned sp). zstep.
    apply evt_done.
    eapply HK; [exact FRM | | | | exact EF | exact EL | exact ES | lia].
    - split; [exact (art_of_munch RT AF Σ mb _ lo W HA ltac:(rewrite ES; exact LOR) (pd_fpok Σ used SR) MU WM)|].
      split; [exact MI|]. split; [exact (wmono_trans asegs _ _ _ (proj1 MR) WM)| exact ST].
    - exact (proj2 (pd_mrel_step Σ used mb _ SR HA MR MU WM)).
    - apply (abig_intro RT _ _ X bs len). split; [exact XA|]. split; [exact XL|]. split; [exact XN|]. split; [exact LEN|].
      split; [exact ZR|]. split; [exact X8|]. rewrite EF. exact XFR.
  Qed.

  Ltac pd_after_call mm m' PR WM' :=
    let AG := fresh "AG" in
    pose proof (agree_of_pres_ex _ _ _ _ _ mm m' _ PR (fun x H => H)) as AG;
    rt_transport_with mm m' AG WM' ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?repeat_length in Hx; cbv beta;
                                         split; [aclient_tac| lia]).

  Lemma pd_move : forall Σ used F fc mb, pd_srel Σ used -> (used <= cr0)%Z -> frm0 fc -> ART RT Σ mb -> pd_mrel mb ->
    pd_move_k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo mb (fun ms' => aevt RT PMc Σ K ms').
  Proof using AF RTF FDO MST PDH HK.
    intros Σ used F fc mb SR HU FRM HA MR. unfold pd_move_k.
    intros k n xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 mm INV Hk Hn Hkn.
    destruct INV as ((j0 & FR) & (bs & XA & XL) & XN & LEN & ZR & MI & MU & WM & ST).
    pose proof SR as (EF & EL & ES & EC).
    pose proof XNUM as (XN0 & XN1 & XN2 & XN3 & XN4).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof ROOM as ROOM'. pose proof TOP as TOP'. unfold PDCA_STACK, P5A_STACK, LMA_STACK, RT_STACK, USTACK_TOP in ROOM', TOP'.
    destruct XFR as (g & kg & Hin & G1 & G2). rewrite <- EF in Hin.
    apply evt_done.
    assert (ARTm : ART RT Σ mm) by exact (art_of_munch RT AF Σ mb mm lo W HA ltac:(rewrite ES; exact LOR) (pd_fpok Σ used SR) MU WM).
    assert (MRm : pd_mrel mm) by exact (pd_mrel_step Σ used mb mm SR HA MR MU WM).
    assert (COK : call_ok RT Σ mm (Z_to_bv 64 (SP + -64)) lo).
    { unfold call_ok. rewrite unsigned_lit by lia. split; [exact ST|]. split; [rewrite ES; exact LOR|]. unfold RT_STACK, USTACK_TOP.
      split; [lia|]. split; [lia| Z.div_mod_to_equations; lia]. }
    assert (XFRm : exists f c, In (f, c) (rt_frames RT Σ) /\ (f <= X)%Z /\ (X + Z.of_nat (length bs) <= f + fs_size c - 8)%Z)
      by (exists g, kg; split; [exact Hin| rewrite XL; lia]).
    eapply (aevt_memmove_u8 RT AF RTF PMc FDO MST Σ K mm X bs 63 lo (Z_to_bv 64 (SP + -64)) XA X8 ltac:(lia) ltac:(rewrite XL; lia) ltac:(rewrite XL; lia)
              ltac:(rewrite XL; lia) ZR XFRm ARTm MI COK) with (dz := (8 * k)%Z) (sz := 0%Z) (nz := (8 * n)%Z);
      [reflexivity | f_equal; lia | reflexivity | lia | lia | lia | rewrite XL; lia | rewrite XL; lia | lia | exact FRM | ].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' bs' FRM' RA PR XA' XL'.
    rewrite ?unsigned_lit in RA, PR by lia. destruct RA as (ART' & MI' & WM' & ST').
    pose proof (repeat_length (Z_to_bv 8 0) 63) as RL.
    clear XA. pd_after_call mm m' PR WM'.
    assert (MR' : pd_mrel m') by (eapply (pd_mrel_ex Σ used mm m' _ _ SR MRm WM' PR); lia).
    clear MU WM MI ST.
    pose proof (munch_refl W m') as MU1. pose proof (wmono_refl asegs m') as WM1. set (mb1 := m') in MU1 at 1, WM1 at 1.
    apply (aevt_evt RT AF PMc MST). num_ret_pc.
    astep. astep. astep. astep. apply evt_done.
    lazymatch goal with |- aevt _ _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (ART1 : ART RT Σ m1) by exact (art_of_munch RT AF Σ mb1 m1 lo W ART' ltac:(rewrite ES; exact LOR) (pd_fpok Σ used SR) MU1 WM1);
      assert (MR1 : pd_mrel m1) by exact (pd_mrel_step Σ used mb1 m1 SR ART' MR' MU1 WM1) end.
    assert (COK1 : call_ok RT Σ m' (Z_to_bv 64 (SP + -64)) lo).
    { unfold call_ok. rewrite unsigned_lit by lia. split; [exact ST'|]. split; [rewrite ES; exact LOR|]. unfold RT_STACK, USTACK_TOP.
      split; [lia|]. split; [lia| Z.div_mod_to_equations; lia]. }
    assert (XFR1 : exists f c, In (f, c) (rt_frames RT Σ) /\ (f <= X)%Z /\ (X + Z.of_nat (length bs') <= f + fs_size c - 8)%Z)
      by (exists g, kg; split; [exact Hin| rewrite XL', XL; lia]).
    eapply (aevt_memset_u8 RT AF RTF PMc FDO MST Σ K m' X bs' 63 lo (Z_to_bv 64 (SP + -64)) XA' X8 ltac:(lia) ltac:(rewrite XL', XL; lia) ltac:(rewrite XL', XL; lia)
              ltac:(rewrite XL', XL; lia) ZR XFR1 ART1 MI' COK1) with (dz := 0%Z) (nz := (8 * k)%Z) (cb := Z_to_bv 8 0);
      [f_equal; lia | reflexivity | reflexivity | lia | lia | rewrite XL', XL; lia | lia | exact FRM' | ].
    intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F'' fc'' m'' bs'' FRM'' RA2 PR2 XA'' XL''.
    rewrite ?unsigned_lit in RA2, PR2 by lia. destruct RA2 as (ART'' & MI'' & WM'' & ST'').
    clear XA' AG. pd_after_call m' m'' PR2 WM''.
    assert (MR'' : pd_mrel m'') by (eapply (pd_mrel_ex Σ used m' m'' _ _ SR MR1 WM'' PR2); lia).
    assert (INV'' : PDINV ra sp s0 s1 s2 s3 s4 s5 X lo m'' m'' n).
    { split; [exists j0; exact FR|]. split; [exists bs''; split; [exact XA''| lia]|]. split; [exact XN|]. split; [exact LEN|]. split; [exact ZR|].
      split; [exact MI''|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact ST'']. }
    apply (aevt_evt RT AF PMc MST). num_ret_pc.
    eapply evt_eq; [| eapply (pd_b2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F'' fc'' X lo m'' ROOM TOP X8 XN0 XN1 XN2 (conj XN3 XN4) _
                                (pd_exit Σ used F'' fc'' m'' SR HU FRM'' ART'' MR'') k n); [exact INV'' | lia | lia]].
    num_st_eq.
  Qed.

  Lemma pd_entry : forall (e n : Z) F fc t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 bs,
    frm0 fc -> ART RT Σ0 me -> mem_inv asegs me -> stk asegs me lo SP ->
    u8arr asegs me X bs -> length bs = 496%nat -> rw_cells asegs me (X + 496) [C2 (Z_to_bv 64 n)] -> (0 <= n <= 62)%Z ->
    bytes_at asegs me (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) ->
    (0 <= e < 135 * (cr0 + 1))%Z -> (0 <= cr0)%Z -> (e < 2147483648)%Z ->
    aevt RT PMc Σ0 K
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xe096c) fc None me (seg_rom asegs)).
  Proof using AF RTF FDO MST HP5 PDH HK.
    intros e n F fc t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 bs FRM HA MI ST XA XL XN LEN ZR He Hcr He31.
    pose proof XNUM as (XN0 & XN1 & XN2 & XN3 & XN4).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof ROOM as ROOM'. pose proof TOP as TOP'. unfold PDCA_STACK, P5A_STACK, LMA_STACK, RT_STACK, USTACK_TOP in ROOM', TOP'.
    pose proof (af_sp0_range RT AF Σ0 me HA) as SP0R. unfold SEGTOP_A, STACK_WIN, USTACK_TOP in SP0R. pose proof LOR as LOR'. unfold STACK_WIN in LOR'.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (repeat_length (Z_to_bv 8 0) 63) as RL.
    destruct (af_client_consts RT AF Σ0 me HA) as (G1 & G2 & _). unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SHB in G1, G2.
    assert (SR0 : pd_srel Σ0 0) by (unfold pd_srel; repeat split; lia).
    assert (MR0 : pd_mrel me) by (split; [apply wmono_refl| apply pres_fp_refl]).
    apply (aevt_evt RT AF PMc MST).
    pose proof (munch_refl W me) as MU. pose proof (wmono_refl asegs me) as WM.
    set (mb := me) in MU at 1, WM at 1.
    step.
    carve_frame 64%nat ST.
    apply (rw_cells_split_CB asegs me _ [] 64 junk [] [8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 7 step. do 7 zstep.
    clear G1 G2.
    apply evt_done.
    lazymatch goal with |- aevt _ _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (ART1 : ART RT Σ0 m1) by exact (art_of_munch RT AF Σ0 mb m1 lo W HA LOR (pd_fpok Σ0 0%Z SR0) MU WM);
      assert (MR1 : pd_mrel m1) by exact (pd_mrel_step Σ0 0%Z mb m1 SR0 HA MR0 MU WM) end.
    eapply (HP5 Σ0) with (X := X) (e := e) (cr := cr0) (lo := lo); rewrite ?unsigned_lit by lia; unfold P5A_STACK, LMA_STACK, RT_STACK, USTACK_TOP;
      [ exact ETP | exact FRM | exact FRL | lia | lia | lia | exact CR0 | exact ART1 | eassumption | exact ST | exact LOR | lia | lia
      | Z.div_mod_to_equations; lia
      | apply (abig_intro RT _ _ X bs n); split; [eassumption|]; split; [exact XL|]; split; [eassumption|]; split; [exact LEN|];
        split; [eassumption|]; split; [exact X8| exact XFR]
      | ].
    intros Σ' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' FRM' RA PR AB EF' EL' ES' EC'.
    rewrite ?unsigned_lit in RA, PR by lia.
    destruct RA as (ART' & MI' & WM' & ST').
    assert (SR' : pd_srel Σ' cr0) by (unfold pd_srel; repeat split; try assumption; lia).
    destruct (abig_elim RT _ _ _ AB) as (bs' & n' & XA' & XL' & XN' & LEN' & ZR' & _ & _).
    lazymatch type of PR with rt_pres_fp _ _ _ _ ?mm _ =>
      pose proof (agree_pres_fp _ _ _ _ mm m' (fun x => aclient (rt_live RT Σ0) (rt_frames RT Σ0) (SP + -64) x /\ outside [(X, (X + 504)%Z)] x) PR (fun x H => H)) as AG;
      repeat match goal with H : u8arr asegs mm _ _ |- _ => clear H | H : bytes_at asegs mm _ _ |- _ => clear H | H : rw_cells asegs mm (X + 496) _ |- _ => clear H end;
      rt_transport_with mm m' AG WM' ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbv beta; split; [aclient_tac| cbn [outside]; lia]);
      assert (MR' : pd_mrel m') by
        (destruct MR1 as [WM0 PR0]; split; [exact (wmono_trans asegs _ _ _ WM0 WM')|]; eapply pres_fp_trans; [exact PR0|]; eapply pres_fp_sp; [exact PR| lia])
    end.
    assert (INV' : PDINV ra sp s0 s1 s2 s3 s4 s5 X lo m' m' n').
    { split; [eexists; exact FR|]. split; [exists bs'; split; [exact XA'| exact XL']|]. split; [exact XN'|]. split; [exact LEN'|]. split; [exact ZR'|].
      split; [exact MI'|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact ST']. }
    apply (aevt_evt RT AF PMc MST). num_ret_pc.
    eapply evt_eq; [| eapply (pd_b1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F' fc' X lo m' ROOM TOP X8 XN0 XN1 XN2 (conj XN3 XN4) _
                                (pd_exit Σ' cr0 F' fc' m' SR' ltac:(lia) FRM' ART' MR') (pd_move Σ' cr0 F' fc' m' SR' ltac:(lia) FRM' ART' MR') e n'); [exact INV' | lia]].
    num_st_eq.
  Qed.
End PDTOP.

Theorem pdca_ok : forall RT, art_facts RT -> rt_contracts_f RT ->
  forall PMc, fdfs_only PMc -> mat_stable PMc -> p5a_stmt RT PMc -> pdca_stmt RT PMc.
Proof.
  intros RT AF RTF PMc FDO MST HP5. unfold pdca_stmt.
  intros Σ K ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m X e cr lo
    ETP FRM FRL He Hcr He31 CR ART0 MI ST LOR ROOM TOP SP16 AB HK.
  destruct (abig_elim RT _ _ _ AB) as (bs & n & RAW).
  pose proof (abig_facts RT AF Σ m X bs n lo ART0 LOR RAW) as XNUM.
  destruct RAW as (XA & XL & XN & LEN & ZR & X8 & XFR).
  eapply (pd_entry RT AF RTF PMc FDO MST HP5 Σ K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X lo cr m ETP ROOM TOP SP16 LOR FRL X8 XFR XNUM CR HK
            e n F fc t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 bs); try eassumption; lia.
Qed.
