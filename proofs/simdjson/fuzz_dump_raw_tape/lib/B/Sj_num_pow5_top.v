(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_abig Sj_num_acall Sj_num_bcall Sj_num_brel Sj_num_lits Sj_num_pow5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_ptr_hook | asan_zr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.

Section P5TOP.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RTF : rt_contracts_f RT.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.
  Hypothesis HLM : lmb_stmt RT PMc.

  Variables (Σ0 : rts RT) (K : config -> Prop).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (X lo cr0 e0 len0 : Z) (bs0 : list byte) (me : mem).
  Notation SP := (bv_unsigned sp).
  Notation C := (bignorm_b bs0 len0 /\ len0 + 15 <= 62 /\ e0 <= 328)%Z.
  Hypothesis ETP : tp = Z_to_bv 64 B_TP.
  Hypothesis ROOM : (lo + P5B_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis LOR : (rt_sp0 RT Σ0 - STACK_WIN <= lo)%Z.
  Hypothesis FRL : (length (rt_frames RT Σ0) < FRAMES_MAX)%nat.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis XFR : exists f c, In (f, c) (rt_frames RT Σ0) /\ (f <= X)%Z /\ (X + 504 <= f + fs_size c - 8)%Z.
  Hypothesis XNUM : (0x6ce000 <= X /\ X + 504 <= lo
                     /\ (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)
                     /\ 0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo)%Z.
  Hypothesis CR0 : (cr0 <= rt_credit RT Σ0)%Z.
  Hypothesis ER : (0 <= e0 < 135 * (cr0 + 1) /\ 0 <= cr0 /\ e0 < 2147483648)%Z.
  Hypothesis HK : big_k RT PMc Σ0 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 me X lo cr0 (p5b_G bs0 len0 e0).
  Collection P5H := ETP ROOM TOP SP16 LOR FRL X8 XFR XNUM CR0 ER.

  Notation W := [(SP - 48, SP); (X, X + 504)]%Z.
  Notation mrel := (b_mrel RT Σ0 SP X me).
  Notation srel := (b_srel RT Σ0).

  Lemma p5_room : (lo + 48 <= SP /\ SP <= USTACK_TOP /\ lo + 48 + 256 + 65536 <= SP)%Z.
  Proof using P5H. pose proof ROOM as R. pose proof TOP as T. unfold P5B_STACK, LMB_STACK, RT_STACK, USTACK_TOP in R, T |- *. lia. Qed.

  Lemma p5_hcl : C -> (len0 + 15 <= 62 /\ 0 <= e0 <= 328)%Z.
  Proof using P5H. intros (_ & H1 & H2). destruct ER as (E1 & _). lia. Qed.

  Lemma p5_zr_out : forall a, (X / 8 + 2147450880 <= a < X / 8 + 2147450880 + Z.of_nat 63)%Z -> outside W a.
  Proof using P5H.
    intros a Ha. destruct XNUM as (XN0 & XN1 & XN2 & XN3 & XN4). destruct p5_room as (R1 & R2 & _). cbn [outside].
    change (Z.of_nat 63) with 63%Z in Ha. split; [lia|]. split; [lia| exact I].
  Qed.

  Lemma p5_shpl : forall Σ used mb, srel Σ used -> ART RT Σ mb -> forall m', munch W mb m' -> wmono bsegs mb m' -> shz m' 0x2b5a0 640.
  Proof using AF P5H.
    intros Σ used mb SR HA m' MU WM. destruct p5_room as (R1 & R2 & _). pose proof SR as (_ & _ & ES & _).
    change 640%Z with (8 * (640 / 8))%Z.
    eapply (shzp_lits RT AF Σ mb lo W 0x2b5a0 640 (num_lits_of_af RT AF) HA ltac:(rewrite ES; exact LOR) (b_fpok RT Σ0 SP lo X 48 LOR ltac:(lia) R1 R2 XFR Σ used SR));
      [unfold NUM_LITS; right; left; reflexivity | exact MU | exact WM].
  Qed.

  Lemma p5_kret : forall Σ used F fc mb, srel Σ used -> (used <= cr0)%Z -> frm0 fc -> ART RT Σ mb -> mrel mb ->
    bytes_at bsegs mb (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) ->
    p5_ret_k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo len0 mb C (fun ms' => aevt RT PMc Σ K ms').
  Proof using AF P5H HK.
    intros Σ used F fc mb SR HU FRM HA MR ZR. unfold p5_ret_k. intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mm bs len r XA XL XN LEN MI MU WM ST HR.
    destruct p5_room as (R1 & R2 & _). pose proof SR as (EF & EL & ES & EC).
    eapply HK; [exact FRM | | | | | exact EF | exact EL | exact ES | lia].
    - split; [exact (b_art RT AF Σ0 SP lo X 48 LOR ltac:(lia) R1 R2 XFR Σ used mb mm SR HA MU WM)|].
      split; [exact MI|]. split; [exact (wmono_trans bsegs _ _ _ (proj1 MR) WM)| exact ST].
    - exact (proj2 (b_mrel_step RT AF Σ0 SP lo X 48 me LOR ltac:(lia) R1 R2 XFR Σ used mb mm SR HA MR MU WM)).
    - apply (b_bbig RT Σ0 X XFR Σ used mm bs len SR X8 XA XL XN LEN). exact (zr_munch W mb mm _ 63 ZR p5_zr_out MU).
    - unfold p5b_G. intros H1 H2 H3. destruct (HR (conj H1 (conj H2 H3))) as (-> & H4 & H5). split; [reflexivity|]. split; assumption.
  Qed.

  Lemma p5_klm : forall (f : nat) (k : Z) Σ F fc mb, srel Σ k -> (0 <= k <= cr0)%Z -> (e0 - 135 * k < 135 * (Z.of_nat f + 1))%Z ->
    frm0 fc -> ART RT Σ mb -> mrel mb -> bytes_at bsegs mb (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) ->
    p5_lm_k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo len0 e0 mb C (fun ms' => aevt RT PMc Σ K ms') (fun k' => (k' = k)%Z).
  Proof using AF RTF FDO MST HLM P5H HK.
    induction f as [|f IH]; intros k Σ F fc mb SR Hk Hf FRM HA MR ZR; unfold p5_lm_k;
      intros k' len xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 mm -> INV Hk0 He HP; [exfalso; lia|].
    destruct INV as (FR & (bs & XA & XL & NB) & XN & LEN & MI & MU & WM & ST).
    destruct p5_room as (R1 & R2 & R3). pose proof SR as (EF & EL & ES & EC).
    pose proof XNUM as (XN0 & XN1 & XN2 & XN3 & XN4). pose proof ER as (E1 & E2 & E3).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof TOP as TOP'. unfold USTACK_TOP in TOP', R2.
    pose proof (repeat_length (Z_to_bv 8 0) 63) as RL.
    apply evt_done.
    assert (ARTm : ART RT Σ mm) by exact (b_art RT AF Σ0 SP lo X 48 LOR ltac:(lia) R1 ltac:(unfold USTACK_TOP; lia) XFR Σ k mb mm SR HA MU WM).
    assert (MRm : mrel mm) by exact (b_mrel_step RT AF Σ0 SP lo X 48 me LOR ltac:(lia) R1 ltac:(unfold USTACK_TOP; lia) XFR Σ k mb mm SR HA MR MU WM).
    assert (ZRm : bytes_at bsegs mm (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63)) by exact (zr_munch W mb mm _ 63 ZR p5_zr_out MU).
    eapply (HLM Σ) with (X := X) (lo := lo) (bs := bs) (len := len); rewrite ?unsigned_lit by lia; unfold LMB_STACK, RT_STACK, USTACK_TOP;
      [ exact ETP | exact FRM | rewrite EF; exact FRL | lia | exact ARTm | exact MI | exact ST | rewrite ES; exact LOR | lia | lia
      | Z.div_mod_to_equations; lia
      | exact (b_bbig RT Σ0 X XFR Σ k mm bs len SR X8 XA XL XN LEN ZRm)
      | ].
    intros Σ' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' bs' len' FRM' RA PR BB' G' EF' EL' ES' EC'.
    rewrite ?unsigned_lit in RA, PR by lia.
    destruct RA as (ART' & MI' & WM' & ST').
    assert (SR' : srel Σ' (k + 1)) by (unfold b_srel; repeat split; [rewrite EF'; exact EF| rewrite EL'; exact EL| rewrite ES'; exact ES| lia]).
    destruct (abig_elim RT _ _ _ (bbig_abig RT Σ' m' X bs' len' BB')) as (bs1 & n1 & _ & _ & _ & _ & ZR' & _ & _).
    destruct BB' as (_ & XL' & XA' & XN' & LEN').
    assert (GC : C -> a0' = Z_to_bv 64 1 /\ bignorm_b bs' len' /\ (len' <= len + 6)%Z).
    { intros HC. apply G'. pose proof (HP HC) as (P1 & P2). pose proof (p5_hcl HC) as (P3 & P4). lia. }
    pose proof (agree_pres_fp _ _ _ _ mm m' (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) (SP + -48) x /\ outside [(X, (X + 504)%Z)] x) PR (fun x H => H)) as AG.
    clear XA XN ZRm.
    rt_transport_with mm m' AG WM' ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbv beta; split; [aclient_tac| cbn [outside]; lia]).
    assert (MR' : mrel m') by (eapply (b_mrel_fp RT Σ0 SP X me Σ k mm m' _ SR MRm WM' PR); lia).
    assert (INV' : P5INV ra sp s0 s1 s2 s3 s4 X lo m' C m' len').
    { split; [exact FR|]. split; [exists bs'; split; [exact XA'| split; [exact XL'| intros HC; exact (proj1 (proj2 (GC HC)))]]|].
      split; [exact XN'|]. split; [exact LEN'|]. split; [exact MI'|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact ST']. }
    apply (aevt_evt RT AF PMc MST). num_ret_pc.
    rewrite <- (Z_to_bv_bv_unsigned a0').
    eapply evt_eq; [| eapply (p5_9fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F' fc' X lo len0 e0 m' C R1 XN0 XN1 X8 p5_hcl
                                (shzp_zr W m' X 63 ZR' X8 ltac:(lia) p5_zr_out) (p5_shpl Σ' (k + 1) m' SR' ART')
                                _ (p5_kret Σ' (k + 1) F' fc' m' SR' ltac:(lia) FRM' ART' MR' ZR')
                                (fun k' => (k' = k + 1)%Z)
                                (IH (k + 1)%Z Σ' F' fc' m' SR' ltac:(lia) ltac:(lia) FRM' ART' MR' ZR')
                                k (bv_unsigned a0')) with (len := len');
                         [reflexivity | exact INV' | lia | lia | intros HC; destruct (GC HC) as (-> & _); reflexivity
                         | intros HC; destruct (GC HC) as (_ & _ & L6); pose proof (HP HC); lia]].
    num_st_eq.
  Qed.

  Lemma p5_top : forall F fc t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    frm0 fc -> ART RT Σ0 me -> mem_inv bsegs me -> stk bsegs me lo SP ->
    u8arr bsegs me X bs0 -> length bs0 = 496%nat -> rw_cells bsegs me (X + 496) [C2 (Z_to_bv 64 len0)] -> (0 <= len0 <= 62)%Z ->
    bytes_at bsegs me (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) ->
    aevt RT PMc Σ0 K
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 e0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 B_POW5) fc None me (seg_rom bsegs)).
  Proof using AF RTF FDO MST HLM P5H HK.
    intros F fc t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 FRM HA MI ST XA XL XN LEN ZR.
    pose proof XNUM as (XN0 & XN1 & XN2 & XN3 & XN4). pose proof ER as (E1 & E2 & E3).
    destruct p5_room as (R1 & R2 & _).
    pose proof (b_consts_of me (af_client_consts RT AF Σ0 me HA)) as GC.
    pose proof (b_srel_0 RT Σ0) as SR0. pose proof (b_mrel_0 RT Σ0 SP X me) as MR0.
    apply (aevt_evt RT AF PMc MST).
    eapply (p5_entry ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo len0 e0 me C R1 XN0 XN1 X8 p5_hcl
              (shzp_zr W me X 63 ZR X8 ltac:(lia) p5_zr_out) (p5_shpl Σ0 0 me SR0 HA)
              _ (p5_kret Σ0 0 F fc me SR0 ltac:(lia) FRM HA MR0 ZR)
              (fun k' => (k' = 0)%Z)
              (p5_klm (Z.to_nat cr0) 0 Σ0 F fc me SR0 ltac:(lia) ltac:(lia) FRM HA MR0 ZR));
      try eassumption; [reflexivity | intros (H & _); exact H | lia].
  Qed.
End P5TOP.

Theorem p5b_ok : forall RT, art_facts RT -> rt_contracts_f RT ->
  forall PMc, fdfs_only PMc -> mat_stable PMc -> lmb_stmt RT PMc -> p5b_stmt RT PMc.
Proof.
  intros RT AF RTF PMc FDO MST HLM. unfold p5b_stmt.
  intros Σ K ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m X e cr lo bs len
    ETP FRM FRL He Hcr He31 CR ART0 MI ST LOR ROOM TOP SP16 BB HK.
  pose proof (bbig_abig RT Σ m X bs len BB) as AB.
  destruct BB as (FO & XL & XA & XN & LEN).
  destruct (abig_elim RT _ _ _ AB) as (bs1 & n1 & RAW).
  pose proof (abig_facts RT AF Σ m X bs1 n1 lo ART0 LOR RAW) as XNUM.
  destruct RAW as (_ & _ & _ & _ & ZR & X8 & XFR).
  eapply (p5_top RT AF RTF PMc FDO MST HLM Σ K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X lo cr e len bs m ETP ROOM TOP SP16 LOR FRL X8 XFR XNUM CR
            ltac:(lia) HK); eassumption.
Qed.
