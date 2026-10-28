(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_abig Sj_num_acall Sj_num_bcall Sj_num_brel Sj_num_shl_top Sj_num_pdc.
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

Section PDTOP.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RTF : rt_contracts_f RT.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.
  Hypothesis HP5 : p5b_stmt RT PMc.

  Variables (Σ0 : rts RT) (K : config -> Prop).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (X lo cr0 e len0 : Z) (bs0 : list byte) (me : mem).
  Notation SP := (bv_unsigned sp).
  Hypothesis ETP : tp = Z_to_bv 64 B_TP.
  Hypothesis ROOM : (lo + PDCB_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis LOR : (rt_sp0 RT Σ0 - STACK_WIN <= lo)%Z.
  Hypothesis FRL : (length (rt_frames RT Σ0) < FRAMES_MAX)%nat.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis XFR : exists f c, In (f, c) (rt_frames RT Σ0) /\ (f <= X)%Z /\ (X + 504 <= f + fs_size c - 8)%Z.
  Hypothesis XNUM : (0x6cd000 <= X /\ X + 504 <= lo
                     /\ (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)
                     /\ 0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo)%Z.
  Hypothesis CR0 : (cr0 <= rt_credit RT Σ0)%Z.
  Hypothesis ER : (0 <= e < 135 * (cr0 + 1) /\ 0 <= cr0 /\ e <= 328)%Z.
  Hypothesis NB0 : bignorm_b bs0 len0.
  Hypothesis CAP : (len0 + 21 <= 62)%Z.
  Hypothesis HK : dc_k RT PMc Σ0 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 me X lo cr0.
  Collection PDH := ETP ROOM TOP SP16 LOR FRL X8 XFR XNUM CR0 ER NB0 CAP.

  Notation W := [(SP - 64, SP); (X, X + 504)]%Z.
  Notation mrel := (b_mrel RT Σ0 SP X me).
  Notation srel := (b_srel RT Σ0).

  Lemma pd_room : (lo + 64 <= SP /\ SP <= USTACK_TOP /\ lo + 48 + 48 + 256 + 65536 <= SP)%Z.
  Proof using PDH. pose proof ROOM as R. pose proof TOP as T. unfold PDCB_STACK, P5B_STACK, LMB_STACK, RT_STACK, USTACK_TOP in R, T |- *. lia. Qed.

  Lemma pd_zr_out : forall a, (X / 8 + 2147450880 <= a < X / 8 + 2147450880 + Z.of_nat 63)%Z -> outside W a.
  Proof using PDH.
    intros a Ha. destruct XNUM as (XN0 & XN1 & XN2 & XN3 & XN4). destruct pd_room as (R1 & R2 & _). cbn [outside].
    change (Z.of_nat 63) with 63%Z in Ha. split; [lia|]. split; [lia| exact I].
  Qed.

  Lemma pd_kret : forall Σ used F fc mb, srel Σ used -> (used <= cr0)%Z -> frm0 fc -> ART RT Σ mb -> mrel mb ->
    bytes_at bsegs mb (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) ->
    pd_ret_k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo mb (fun ms' => aevt RT PMc Σ K ms').
  Proof using AF PDH HK.
    intros Σ used F fc mb SR HU FRM HA MR ZR. unfold pd_ret_k. intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mm bs len XA XL XN LEN MI MU WM ST.
    destruct pd_room as (R1 & R2 & _). pose proof SR as (EF & EL & ES & EC).
    eapply HK; [exact FRM | | | | exact EF | exact EL | exact ES | lia].
    - split; [exact (b_art RT AF Σ0 SP lo X 64 LOR ltac:(lia) R1 R2 XFR Σ used mb mm SR HA MU WM)|].
      split; [exact MI|]. split; [exact (wmono_trans bsegs _ _ _ (proj1 MR) WM)| exact ST].
    - exact (proj2 (b_mrel_step RT AF Σ0 SP lo X 64 me LOR ltac:(lia) R1 R2 XFR Σ used mb mm SR HA MR MU WM)).
    - apply (bbig_abig RT Σ mm X bs len). apply (b_bbig RT Σ0 X XFR Σ used mm bs len SR X8 XA XL XN LEN). exact (zr_munch W mb mm _ 63 ZR pd_zr_out MU).
  Qed.

  Lemma pd_top : forall F fc t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    frm0 fc -> ART RT Σ0 me -> mem_inv bsegs me -> stk bsegs me lo SP ->
    u8arr bsegs me X bs0 -> length bs0 = 496%nat -> rw_cells bsegs me (X + 496) [C2 (Z_to_bv 64 len0)] -> (0 <= len0 <= 62)%Z ->
    bytes_at bsegs me (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) ->
    aevt RT PMc Σ0 K
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 B_PDC) fc None me (seg_rom bsegs)).
  Proof using AF RTF FDO MST HP5 PDH HK.
    intros F fc t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 FRM HA MI ST XA XL XN LEN ZR.
    pose proof XNUM as (XN0 & XN1 & XN2 & XN3 & XN4). pose proof ER as (E1 & E2 & E3).
    destruct pd_room as (R1 & R2 & R3). unfold USTACK_TOP in R2.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof TOP as TOP'. unfold USTACK_TOP in TOP'.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    pose proof (repeat_length (Z_to_bv 8 0) 63) as RL.
    destruct (b_consts_of me (af_client_consts RT AF Σ0 me HA)) as (G1 & G2).
    pose proof (b_srel_0 RT Σ0) as SR0. pose proof (b_mrel_0 RT Σ0 SP X me) as MR0.
    unfold B_PDC. apply (aevt_evt RT AF PMc MST).
    pose proof (munch_refl W me) as MU. pose proof (wmono_refl bsegs me) as WM.
    set (mb := me) in MU at 1, WM at 1.
    step.
    carve_frame 48%nat ST.
    apply (rw_cells_split_CB bsegs me _ [] 48 junk [] [15;1;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
    do 4 step. do 7 zstep.
    clear G1 G2.
    lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) => change (c0 :: c1 :: rest) with ([c0] ++ [c1] ++ rest) in FR end.
    apply num_rw_cells_app in FR. destruct FR as [PAD FR]. apply num_rw_cells_app in FR. destruct FR as [TC FR].
    cbn [cells_size csize Nat.add] in TC, FR.
    replace (SP + -48 + Z.of_nat 15)%Z with (SP + -33)%Z in TC, FR by lia.
    replace (SP + -33 + Z.of_nat 1)%Z with (SP + -32)%Z in FR by lia.
    destruct (num_cb1_c1 _ _ _ _ TC) as [tb0 TC1]. clear TC.
    apply evt_done.
    lazymatch goal with |- aevt _ _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (ART1 : ART RT Σ0 m1) by exact (b_art RT AF Σ0 SP lo X 64 LOR ltac:(lia) R1 ltac:(unfold USTACK_TOP; lia) XFR Σ0 0 mb m1 SR0 HA MU WM);
      assert (MR1 : mrel m1) by exact (b_mrel_step RT AF Σ0 SP lo X 64 me LOR ltac:(lia) R1 ltac:(unfold USTACK_TOP; lia) XFR Σ0 0 mb m1 SR0 HA MR0 MU WM) end.
    eapply (HP5 Σ0) with (X := X) (e := e) (cr := cr0) (lo := lo) (bs := bs0) (len := len0); rewrite ?unsigned_lit by lia; unfold P5B_STACK, LMB_STACK, RT_STACK, USTACK_TOP;
      [ exact ETP | exact FRM | exact FRL | lia | lia | lia | exact CR0 | exact ART1 | eassumption | exact ST | exact LOR | lia | lia
      | Z.div_mod_to_equations; lia
      | apply (b_bbig RT Σ0 X XFR Σ0 0 _ bs0 len0 SR0 X8); eassumption
      | ].
    intros Σ' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' bs' len' FRM' RA PR BB' G' EF' EL' ES' EC'.
    rewrite ?unsigned_lit in RA, PR by lia.
    destruct RA as (ART' & MI' & WM' & ST').
    destruct (G' NB0 ltac:(lia) E3) as (-> & NB' & LEN15).
    assert (SR' : srel Σ' cr0) by (unfold b_srel; repeat split; try assumption; lia).
    destruct (abig_elim RT _ _ _ (bbig_abig RT Σ' m' X bs' len' BB')) as (bs1 & n1 & _ & _ & _ & _ & ZR' & _ & _).
    destruct BB' as (_ & XL' & XA' & XN' & LEN').
    lazymatch type of PR with rt_pres_fp _ _ _ _ ?mm _ =>
      pose proof (agree_pres_fp _ _ _ _ mm m' (fun x => aclient (rt_live RT Σ0) (rt_frames RT Σ0) (SP + -48) x /\ outside [(X, (X + 504)%Z)] x) PR (fun x H => H)) as AG;
      repeat match goal with H : u8arr bsegs mm _ _ |- _ => clear H | H : bytes_at bsegs mm _ _ |- _ => clear H | H : rw_cells bsegs mm (X + 496) _ |- _ => clear H end;
      rt_transport_with mm m' AG WM' ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbv beta; split; [aclient_tac| cbn [outside]; lia]);
      assert (MR' : mrel m') by (eapply (b_mrel_fp RT Σ0 SP X me Σ0 0 mm m' _ SR0 MR1 WM' PR); lia)
    end.
    clear AG MU WM.

    apply (aevt_evt RT AF PMc MST). num_ret_pc.
    pose proof (munch_refl W m') as MU. pose proof (wmono_refl bsegs m') as WM. set (mb1 := m') in MU at 1, WM at 1.
    bstep. if_cases KA0; zify_cond KA0; [exfalso; lia|].
    bstep. bstep. bstep. bstep.
    rewrite (Z.mod_small e 4294967296) by lia.
    apply evt_done.
    eapply (shlb_ok RT AF RTF PMc FDO MST Σ') with (X := X) (n := e) (lo := lo) (bs := bs') (len := len'); rewrite ?unsigned_lit by lia; unfold SHLB_STACK, RT_STACK, USTACK_TOP;
      [ exact ETP | exact FRM' | lia | exact ART' | exact MI' | exact ST' | rewrite ES'; exact LOR | lia | lia
      | Z.div_mod_to_equations; lia
      | apply (b_bbig RT Σ0 X XFR Σ' cr0 m' bs' len' SR' X8 XA' XL' XN' LEN' ZR')
      | ].
    intros Σ'' t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F'' fc'' m'' bs'' len'' FRM'' RA2 PR2 BB'' G'' EF'' EL'' ES'' EC''.
    rewrite ?unsigned_lit in RA2, PR2 by lia.
    destruct RA2 as (ART'' & MI'' & WM'' & ST'').
    assert (E64 : (0 <= e / 64 <= 5)%Z) by (Z.div_mod_to_equations; lia).
    destruct (G'' NB' ltac:(lia)) as (_ & NB'' & _).
    assert (SR'' : srel Σ'' cr0) by (unfold b_srel; destruct SR' as (S1 & S2 & S3 & S4); repeat split; [rewrite EF''; exact S1| rewrite EL''; exact S2| rewrite ES''; exact S3| lia]).
    destruct (abig_elim RT _ _ _ (bbig_abig RT Σ'' m'' X bs'' len'' BB'')) as (bs2 & n2 & _ & _ & _ & _ & ZR'' & _ & _).
    destruct BB'' as (_ & XL'' & XA'' & XN'' & LEN'').
    lazymatch type of PR2 with rt_pres_fp _ _ _ _ ?mm _ =>
      pose proof (agree_pres_fp _ _ _ _ mm m'' (fun x => aclient (rt_live RT Σ') (rt_frames RT Σ') (SP + -48) x /\ outside [(X, (X + 504)%Z)] x) PR2 (fun x H => H)) as AG;
      repeat match goal with H : u8arr bsegs mm _ _ |- _ => clear H | H : bytes_at bsegs mm _ _ |- _ => clear H | H : rw_cells bsegs mm (X + 496) _ |- _ => clear H end;
      rt_transport_with mm m'' AG WM'' ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; cbv beta; split; [aclient_tac| cbn [outside]; lia]);
      assert (MR'' : mrel m'') by (eapply (b_mrel_fp RT Σ0 SP X me Σ' cr0 mm m'' _ SR' MR' WM'' PR2); lia)
    end.
    assert (INV'' : PDINV ra sp s0 s1 s2 X lo m'' m'' len'' tb0).
    { split; [eexists; exact PAD|]. split; [exact TC1|]. split; [exact FR|]. split; [exists bs''; split; [exact XA''| split; [exact XL''| exact NB'']]|].
      split; [exact XN''|]. split; [exact LEN''|]. split; [exact MI''|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact ST'']. }
    pose proof (b_consts_of m'' (af_client_consts RT AF Σ'' m'' ART'')) as GC''.
    pose proof SR'' as (S1 & S2 & S3 & S4).
    apply (aevt_evt RT AF PMc MST). num_ret_pc.
    eapply evt_eq; [| eapply (pd_ca8 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F'' fc'' X lo m'' R1 ltac:(unfold USTACK_TOP; lia) XN0 XN1 X8
                                (shzp_zr W m'' X 63 ZR'' X8 ltac:(lia) pd_zr_out)
                                (shzp_stack RT AF Σ'' m'' lo W (SP - 64) 64 ART'' ltac:(rewrite S3; exact LOR) (b_fpok RT Σ0 SP lo X 64 LOR ltac:(lia) R1 ltac:(unfold USTACK_TOP; lia) XFR Σ'' cr0 SR'')
                                   ltac:(rewrite S3; lia) ltac:(unfold USTACK_TOP; lia) ltac:(Z.div_mod_to_equations; lia))
                                _ (pd_kret Σ'' cr0 F'' fc'' m'' SR'' ltac:(lia) FRM'' ART'' MR'' ZR'')) with (len := len'') (tb := tb0); [exact INV'' | exact GC'']].
    num_st_eq.
  Qed.
End PDTOP.

Theorem pdcb_ok : forall RT, art_facts RT -> rt_contracts_f RT ->
  forall PMc, fdfs_only PMc -> mat_stable PMc -> p5b_stmt RT PMc -> pdcb_stmt RT PMc.
Proof.
  intros RT AF RTF PMc FDO MST HP5. unfold pdcb_stmt.
  intros Σ K ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m X e cr lo bs len
    ETP FRM FRL He Hcr He328 CR ART0 MI ST LOR ROOM TOP SP16 BB NB CAP HK.
  pose proof (bbig_abig RT Σ m X bs len BB) as AB.
  destruct BB as (FO & XL & XA & XN & LEN).
  destruct (abig_elim RT _ _ _ AB) as (bs1 & n1 & RAW).
  pose proof (abig_facts RT AF Σ m X bs1 n1 lo ART0 LOR RAW) as XNUM.
  destruct RAW as (_ & _ & _ & _ & ZR & X8 & XFR).
  eapply (pd_top RT AF RTF PMc FDO MST HP5 Σ K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X lo cr e len bs m ETP ROOM TOP SP16 LOR FRL X8 XFR XNUM CR
            ltac:(lia) NB CAP HK); eassumption.
Qed.
