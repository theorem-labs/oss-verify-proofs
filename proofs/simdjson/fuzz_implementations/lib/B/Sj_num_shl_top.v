(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjNumber SjNumU.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_abig Sj_num_acall Sj_num_bcall Sj_num_brel Sj_num_shl.
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

Section SHTOP.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RTF : rt_contracts_f RT.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.

  Variables (Σ0 : rts RT) (K : config -> Prop).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (X lo n len0 : Z) (bs0 : list byte) (me : mem).
  Notation SP := (bv_unsigned sp).
  Notation C := (bignorm_b bs0 len0 /\ len0 + n / 64 + 1 <= 62)%Z.
  Hypothesis ROOM : (lo + SHLB_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis LOR : (rt_sp0 RT Σ0 - STACK_WIN <= lo)%Z.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis XFR : exists f c, In (f, c) (rt_frames RT Σ0) /\ (f <= X)%Z /\ (X + 504 <= f + fs_size c - 8)%Z.
  Hypothesis XNUM : (0x6e0000 <= X /\ X + 504 <= lo
                     /\ (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)
                     /\ 0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo)%Z.
  Hypothesis NR : (0 <= n < 18446744073709551616)%Z.
  Hypothesis HK : big_k RT PMc Σ0 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 me X lo 0 (shlb_G bs0 len0 n).
  Collection SHH := ROOM TOP SP16 LOR X8 XFR XNUM NR.

  Notation W := [(SP - 64, SP); (X, X + 504)]%Z.
  Notation mrel := (b_mrel RT Σ0 SP X me).
  Notation srel := (b_srel RT Σ0).

  Lemma sh_room : (lo + 64 <= SP /\ SP <= USTACK_TOP)%Z.
  Proof using SHH. pose proof ROOM as R. pose proof TOP as T. unfold SHLB_STACK, RT_STACK, USTACK_TOP in R, T |- *. lia. Qed.

  Lemma sh_zr_out : forall a, (X / 8 + 2147450880 <= a < X / 8 + 2147450880 + Z.of_nat 63)%Z -> outside W a.
  Proof using SHH.
    intros a Ha. destruct XNUM as (XN0 & XN1 & XN2 & XN3 & XN4). destruct sh_room as [R1 R2]. cbn [outside].
    change (Z.of_nat 63) with 63%Z in Ha. split; [lia|]. split; [lia| exact I].
  Qed.

  Lemma sh_kret : forall F fc mb, frm0 fc -> ART RT Σ0 mb -> mrel mb ->
    bytes_at bsegs mb (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) ->
    sh_ret_k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo n mb len0 C (fun ms' => aevt RT PMc Σ0 K ms').
  Proof using AF SHH HK.
    intros F fc mb FRM HA MR ZR. unfold sh_ret_k. intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mm bs len r XA XL XN LEN MI MU WM ST HR.
    destruct sh_room as [R1 R2].
    pose proof (b_srel_0 RT Σ0) as SR0.
    eapply HK; [exact FRM | | | | | reflexivity | reflexivity | reflexivity | lia].
    - split; [exact (b_art RT AF Σ0 SP lo X 64 LOR ltac:(lia) R1 R2 XFR Σ0 0 mb mm SR0 HA MU WM)|].
      split; [exact MI|]. split; [exact (wmono_trans bsegs _ _ _ (proj1 MR) WM)| exact ST].
    - exact (proj2 (b_mrel_step RT AF Σ0 SP lo X 64 me LOR ltac:(lia) R1 R2 XFR Σ0 0 mb mm SR0 HA MR MU WM)).
    - apply (b_bbig RT Σ0 X XFR Σ0 0 mm bs len SR0 X8 XA XL XN LEN). exact (zr_munch W mb mm _ 63 ZR sh_zr_out MU).
    - unfold shlb_G. intros H1 H2. destruct (HR (conj H1 H2)) as (-> & H3 & H4). split; [reflexivity|]. split; assumption.
  Qed.

  Lemma sh_kmv : forall F fc mb, frm0 fc -> ART RT Σ0 mb -> mrel mb ->
    bytes_at bsegs mb (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) ->
    sh_move_k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo n mb len0 C (fun ms' => aevt RT PMc Σ0 K ms').
  Proof using AF RTF FDO MST SHH HK.
    intros F fc mb FRM HA MR ZR. unfold sh_move_k.
    intros k len xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 mm INV Hk Hlen Hkl HL HKN.
    destruct INV as (FR & (bs & XA & XL & NB) & XN & LEN & MI & MU & WM & ST).
    destruct sh_room as [R1 R2].
    pose proof (b_srel_0 RT Σ0) as SR0.
    pose proof XNUM as (XN0 & XN1 & XN2 & XN3 & XN4).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof ROOM as ROOM'. pose proof TOP as TOP'. unfold SHLB_STACK, RT_STACK, USTACK_TOP in ROOM', TOP'.
    destruct XFR as (g & kg & Hin & G1 & G2).
    apply evt_done.
    assert (ARTm : ART RT Σ0 mm) by exact (b_art RT AF Σ0 SP lo X 64 LOR ltac:(lia) R1 R2 XFR Σ0 0 mb mm SR0 HA MU WM).
    assert (MRm : mrel mm) by exact (b_mrel_step RT AF Σ0 SP lo X 64 me LOR ltac:(lia) R1 R2 XFR Σ0 0 mb mm SR0 HA MR MU WM).
    assert (ZRm : bytes_at bsegs mm (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63)) by exact (zr_munch W mb mm _ 63 ZR sh_zr_out MU).
    assert (COK : call_ok RT Σ0 mm (Z_to_bv 64 (SP + -64)) lo).
    { unfold call_ok. rewrite unsigned_lit by lia. split; [exact ST|]. split; [exact LOR|]. unfold RT_STACK, USTACK_TOP.
      split; [lia|]. split; [lia| Z.div_mod_to_equations; lia]. }
    assert (XFRm : exists f c, In (f, c) (rt_frames RT Σ0) /\ (f <= X)%Z /\ (X + Z.of_nat (length bs) <= f + fs_size c - 8)%Z)
      by (exists g, kg; split; [exact Hin| rewrite XL; lia]).
    eapply (aevt_memmove_u8N RT AF RTF PMc FDO MST Σ0 K mm X bs 63 lo (Z_to_bv 64 (SP + -64)) XA X8 ltac:(lia) ltac:(rewrite XL; lia) ltac:(rewrite XL; lia)
              ltac:(rewrite XL; lia) ZRm XFRm ARTm MI COK) with (dz := (8 * k)%Z) (sz := 0%Z) (nz := (8 * len)%Z);
      [reflexivity | f_equal; lia | reflexivity | lia | lia | lia | rewrite XL; lia | rewrite XL; lia | lia | exact FRM | ].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' bs' FRM' RA PR XA' XL' TOPL.
    rewrite ?unsigned_lit in RA, PR by lia. destruct RA as (ART' & MI' & WM' & ST').
    pose proof (repeat_length (Z_to_bv 8 0) 63) as RL.
    clear XA.
    pose proof (agree_of_pres_ex _ _ _ _ _ mm m' _ PR (fun x H => H)) as AG.
    rt_transport_with mm m' AG WM' ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?repeat_length in Hx; cbv beta;
                                         split; [aclient_tac| lia]).
    assert (MR' : mrel m') by (eapply (b_mrel_ex RT Σ0 SP X me Σ0 0 mm m' _ _ _ SR0 MRm WM' PR); lia).
    assert (NB' : C -> bignorm_b bs' (len + k)).
    { intros HC. right. specialize (TOPL ltac:(lia)).
      replace (8 * (len + k - 1))%Z with (8 * k + 8 * len - 8)%Z by lia. rewrite TOPL.
      destruct (NB HC) as [?|NZ]; [exfalso; lia|]. replace (0 + 8 * len - 8)%Z with (8 * (len - 1))%Z by lia. exact NZ. }
    assert (INV' : SHINV ra sp s0 s1 s2 s3 s4 s5 s6 X lo m' m' len (len + k) C).
    { split; [exact FR|]. split; [exists bs'; split; [exact XA'| split; [lia| exact NB']]|]. split; [exact XN|]. split; [exact LEN|].
      split; [exact MI'|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact ST']. }
    apply (aevt_evt RT AF PMc MST). num_ret_pc.
    eapply evt_eq; [| eapply (sh_fd4 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F' fc' X lo n m' len0 C ltac:(lia) XN0 XN1 X8 NR ltac:(intros [_ H]; exact H)
                                (shzp_zr W m' X 63 ZRm X8 ltac:(lia) sh_zr_out) _ (sh_kret F' fc' m' FRM' ART' MR' ZRm) k) with (len := len);
                         [exact INV' | lia | lia | lia | intros HC; exact (HL HC) | exact HKN]].
    num_st_eq.
  Qed.

  Lemma sh_top : forall F fc t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    frm0 fc -> ART RT Σ0 me -> mem_inv bsegs me -> stk bsegs me lo SP ->
    u8arr bsegs me X bs0 -> length bs0 = 496%nat -> rw_cells bsegs me (X + 496) [C2 (Z_to_bv 64 len0)] -> (0 <= len0 <= 62)%Z ->
    bytes_at bsegs me (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) ->
    aevt RT PMc Σ0 K
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 B_SHL) fc None me (seg_rom bsegs)).
  Proof using AF RTF FDO MST SHH HK.
    intros F fc t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 FRM HA MI ST XA XL XN LEN ZR.
    pose proof XNUM as (XN0 & XN1 & XN2 & XN3 & XN4).
    destruct sh_room as [R1 R2].
    pose proof (b_consts_of me (af_client_consts RT AF Σ0 me HA)) as GC.
    apply (aevt_evt RT AF PMc MST).
    eapply (sh_entry ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X lo n me len0 C R1 XN0 XN1 X8 NR ltac:(intros [_ H]; exact H)
              (shzp_zr W me X 63 ZR X8 ltac:(lia) sh_zr_out) _ (sh_kret F fc me FRM HA (b_mrel_0 RT Σ0 SP X me) ZR) (sh_kmv F fc me FRM HA (b_mrel_0 RT Σ0 SP X me) ZR));
      try eassumption. intros [H _]; exact H.
  Qed.
End SHTOP.

Theorem shlb_ok : forall RT, art_facts RT -> rt_contracts_f RT ->
  forall PMc, fdfs_only PMc -> mat_stable PMc -> shlb_stmt RT PMc.
Proof.
  intros RT AF RTF PMc FDO MST. unfold shlb_stmt.
  intros Σ K ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m X n lo bs len
    ETP FRM NR ART0 MI ST LOR ROOM TOP SP16 BB HK.
  pose proof (bbig_abig RT Σ m X bs len BB) as AB.
  destruct BB as (FO & XL & XA & XN & LEN).
  destruct (abig_elim RT _ _ _ AB) as (bs1 & n1 & RAW).
  pose proof (abig_facts RT AF Σ m X bs1 n1 lo ART0 LOR RAW) as XNUM.
  destruct RAW as (_ & _ & _ & _ & ZR & X8 & XFR).
  eapply (sh_top RT AF RTF PMc FDO MST Σ K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X lo n len bs m ROOM TOP SP16 LOR X8 XFR XNUM NR HK); eassumption.
Qed.
