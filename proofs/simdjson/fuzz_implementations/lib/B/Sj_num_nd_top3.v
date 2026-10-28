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
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx I_lkit Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_bkit Sj_num_bdefs Sj_num_abig Sj_num_acall Sj_num_acall2 Sj_num_aframe Sj_num_shl_top
  Sj_num_lm_pro Sj_num_lm_kit Sj_num_nd_pro Sj_num_nd_defs Sj_num_nd_a Sj_num_nd_b3 Sj_num_nd_b Sj_num_nd_tkit Sj_num_nd_top Sj_num_nd_top2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_zc_hook | asan_zcp_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac nnorm ::= nnorm_u.

Section NDTOP3.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RTF : rt_contracts_f RT.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.
  Hypothesis HP5 : p5b_stmt RT PMc.

  Variables (Σ0 : rts RT) (K : config -> Prop).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (X lo d spq f g : Z) (kg : nat) (me : mem) (p2 e cr : Z).
  Notation SP := (bv_unsigned sp).
  Notation S := (f / 8 + 2147450880)%Z.
  Hypothesis ETP : tp = Z_to_bv 64 B_TP.
  Hypothesis ROOM : (lo + NDCB_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis LOR : (rt_sp0 RT Σ0 - STACK_WIN <= lo)%Z.
  Hypothesis FRL : (length (rt_frames RT Σ0) + 2 <= FRAMES_MAX)%nat.
  Hypothesis HE : (0 <= e < 135 * (cr + 1))%Z.
  Hypothesis HCR : (0 <= cr)%Z.
  Hypothesis HER : (e <= NDCB_RANGE)%Z.
  Hypothesis CRD : (cr + 1 <= rt_credit RT Σ0)%Z.
  Hypothesis PR : (- NDCB_RANGE <= p2 <= NDCB_RANGE)%Z.
  Hypothesis SPQ : ((d = 0 \/ d = 16) /\ spq = SP - 160 - d)%Z.
  Hypothesis NF : (f mod 64 = 0 /\ 0x6e0000 <= f /\ f + 1016 <= lo /\ (f + 1016 <= S \/ S + 127 <= f) /\ 0 <= S /\ S + 127 <= lo)%Z.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis XG : In (g, kg) (rt_frames RT Σ0) /\ (g <= X)%Z /\ (X + 504 <= g + fs_size kg - 8)%Z.
  Hypothesis XNUM : (0x6e0000 <= X /\ X + 504 <= lo /\ (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)
                     /\ 0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo)%Z.
  Hypothesis SEP : ((X + 504 <= f \/ f + 1024 <= X) /\ (X + 504 <= S \/ S + 128 <= X)
                    /\ (X / 8 + 2147450880 + 63 <= f \/ f + 1024 <= X / 8 + 2147450880)
                    /\ (X / 8 + 2147450880 + 63 <= S \/ S + 128 <= X / 8 + 2147450880))%Z.

  Hypothesis HK : dc_k RT PMc Σ0 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 me X lo (cr + 1).
  Collection TOPH := AF RTF FDO MST HP5 ETP ROOM TOP SP16 LOR FRL HE HCR HER CRD PR SPQ NF X8 XG XNUM SEP HK.

  Notation MREL := (nd_mrel RT Σ0 sp X me).
  Notation PARK := (nd_park ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo d spq f).
  Notation QΣ Σ := (fun ms' => aevt RT PMc Σ K ms').

  Notation T1 L := (L RT AF RTF PMc FDO MST HP5 Σ0 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X lo d spq f g kg me p2 e cr
                      ETP ROOM TOP SP16 LOR FRL HE HCR HER CRD PR SPQ NF X8 XG XNUM SEP HK) (only parsing).
  Notation nd_srel := (Sj_num_nd_top.nd_srel RT Σ0 f).
  Notation nd_ctx := (Sj_num_nd_top.nd_ctx RT Σ0 ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X lo d spq f me cr).
  Notation TK L Σ SR := (L RT AF Σ0 Σ sp X lo d spq f g kg ROOM TOP LOR (proj1 SR) (proj1 (proj2 SR)) (proj1 (proj2 (proj2 SR))) SPQ NF X8 XG XNUM SEP) (only parsing).
  Notation TKm L Σ SR := (L RT AF Σ0 Σ sp X lo d spq f g kg me ROOM TOP LOR (proj1 SR) (proj1 (proj2 SR)) (proj1 (proj2 (proj2 SR))) SPQ NF X8 XG XNUM SEP) (only parsing).

  Ltac top_env Σ SR :=
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof NF as (N1 & N2 & N3 & N4 & N5 & N6); pose proof XNUM as (Q1 & Q2 & Q3 & Q4 & Q5); pose proof SEP as (E1 & E2 & E3 & E4);
    pose proof (T1 top_spq) as [Hd Hs]; pose proof ROOM as ROOM'; pose proof TOP as TOP'; unfold NDCB_STACK, P5B_STACK, LMB_STACK, RT_STACK, USTACK_TOP in ROOM', TOP';
    pose proof (T1 top_inF Σ _ SR) as HinF; pose proof (f64_8 f (proj1 NF)) as F8; pose proof (eq_refl : fs_size 4 = 1024%Z) as FS4;
    pose proof (proj1 (proj2 XG)) as G1; pose proof (proj2 (proj2 XG)) as G2; pose proof (T1 top_inG Σ _ SR) as HinG;
    pose proof (repeat_length (Z_to_bv 8 0) 63) as RL;
    assert (F32 : ((f + 32) / 8 = f / 8 + 4)%Z) by (replace (f + 32)%Z with (f + 8 * 4)%Z by lia; apply f64_div; exact (proj1 NF)).

  Notation EVA L F fc mb := (L sp gp tp F fc X p2 e lo d spq f mb (T1 top_spq) ROOM TOP (proj1 NF) (conj (proj1 (proj2 NF)) (proj1 (proj2 (proj2 NF))))
                               (proj1 (proj2 (proj2 (proj2 NF)))) (proj2 (proj2 (proj2 (proj2 NF)))) X8
                               (conj (proj1 XNUM) (proj1 (proj2 XNUM))) (proj1 (proj2 (proj2 XNUM))) (proj2 (proj2 (proj2 XNUM))) SEP PR (T1 top_er)) (only parsing).
  Notation EVAa L F fc mb := (L sp gp tp F fc X p2 e lo d spq f mb (T1 top_spq) ROOM TOP (proj1 NF) (conj (proj1 (proj2 NF)) (proj1 (proj2 (proj2 NF))))
                               (proj1 (proj2 (proj2 (proj2 NF)))) (proj2 (proj2 (proj2 (proj2 NF)))) PR (T1 top_er)) (only parsing).
  Ltac nd_after_call mm m' AG WM' :=
    rt_transport_with mm m' AG WM' ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?repeat_length in Hx;
                                         repeat match goal with HL : length _ = 496%nat |- _ => progress (rewrite HL in Hx) end; cbv beta; split; [aclient_tac| first [lia | cbn [outside]; lia]]).

  Ltac nd_site INV CTX :=
    pose proof INV as ((c0 & c8 & c16 & c32 & c40 & SPILL) & (xbs & XA & XL) & XN & LEN & ZR & (tbs & TA & TL) & TN & TLN & TSH & MI & MU & WM);
    unfold nd_W in MU; unfold nd_spill in SPILL;
    lazymatch type of CTX with nd_ctx ?Σ ?used ?fc ?mb =>
      lazymatch type of MU with munch _ _ ?mm =>
        pose proof ((T1 top_ctx_step) Σ used fc mb mm CTX MU WM) as CTXm; pose proof CTXm as (SR & HU & FRM & ARTm & MRm & PKm);
        pose proof PKm as (_ & _ & _ & _ & ST); top_env Σ SR; clear CTX MU WM INV
      end end.

  Lemma nd_kp5 : forall Σ F fc mb, nd_ctx Σ 0 fc mb -> nd_p5_k sp gp tp F fc X p2 e spq f mb (QΣ Σ).
  Proof using TOPH.
    intros Σ F fc mb CTX. unfold nd_p5_k. intros until xlen. intros INV HE0 HQ. nd_site INV CTX.
    pose proof SR as (EF & EL & ES & EC). pose proof HE as HE'. pose proof HER as HER'. unfold NDCB_RANGE in HER'. pose proof CRD as CRD'.
    apply evt_done.
    pose proof ((T1 top_bbig_t) Σ 0%Z mm tbs 1%Z SR TA TL TN ltac:(lia) TSH) as BBT.
    eapply (HP5 Σ) with (X := (f + 32)%Z) (e := e) (cr := cr) (lo := lo) (bs := tbs) (len := 1%Z); rewrite ?unsigned_lit by lia; unfold P5B_STACK, LMB_STACK, RT_STACK, USTACK_TOP;
      [ exact ETP | exact FRM | rewrite EF; cbn [length]; unfold FRAMES_MAX in *; lia | exact HE | exact HCR | lia | lia | exact ARTm | exact MI | exact ST
      | exact ((T1 top_lor1) Σ 0%Z SR) | lia | lia | Z.div_mod_to_equations; lia | exact BBT | ].
    intros Σ' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' bs' len' FRM' RA PRF BB' _ EF' EL' ES' EC'.
    rewrite ?unsigned_lit in RA, PRF by lia.
    assert (SR' : nd_srel Σ' cr) by (unfold nd_srel; rewrite EF', EL', ES'; repeat split; try assumption; lia).
    assert (PRX : rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) spq (f + 32) 504 mm m').
    { intros a Ha Hda. apply PRF; [exact Ha|]. cbn [outside]. split; [lia| exact I]. }
    pose proof ((T1 nd_ctx_call2) Σ Σ' 0%Z cr fc fc' mm m' _ _ CTXm SR' ltac:(lia) FRM' RA PRX ltac:(left; lia)) as CTX'.
    destruct RA as (ART' & MI' & WM' & ST').
    destruct BB' as (_ & TL' & TA' & TN' & TLN').
    pose proof (agree_of_pres_ex _ _ _ _ _ mm m' (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) spq x /\ ~ (f + 32 <= x < f + 32 + 504)%Z) PRX (fun x H => H)) as AG.
    clear TA TN ST MI BBT. nd_after_call mm m' AG WM'.
    replace (f + 32 + 496)%Z with (f + 528)%Z in TN' by lia.
    assert (INV' : nd_inv X spq f m' (repeat (Z_to_bv 8 0) 63) m' xlen len').
    { unfold nd_inv, nd_spill. split; [exists c0, c8, c16, c32, c40; exact SPILL|]. split; [exists xbs; split; [exact XA| exact XL]|].
      split; [exact XN|]. split; [lia|]. split; [exact ZR|]. split; [exists bs'; split; [exact TA'| exact TL']|].
      split; [exact TN'|]. split; [lia|]. split; [exact TSH|]. split; [exact MI'|]. split; [apply munch_refl| apply wmono_refl]. }
    apply (aevt_evt RT AF PMc MST). num_ret_pc.
    eapply evt_eq; [| eapply (EVA nd_2b8 F' fc' m' (QΣ Σ') ((T1 nd_kshlt) Σ' cr F' fc' m' CTX') ((T1 nd_kshlx) Σ' cr F' fc' m' CTX') ((T1 nd_k55c) Σ' cr F' fc' m' CTX') q2); [exact INV' | exact HQ]].
    num_st_eq.
  Qed.

  Lemma nd_kms : forall Σ F fc mb xbs xlen jt, nd_ctx Σ 0 fc mb ->
    u8arr bsegs mb X xbs -> length xbs = 496%nat -> rw_cells bsegs mb (X + 496) [C2 (Z_to_bv 64 xlen)] -> (0 <= xlen <= 62)%Z ->
    bytes_at bsegs mb (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) -> rw_cells bsegs mb (f + 32) [CB 504 jt] ->
    nd_a_mset_k sp gp tp F fc X p2 e spq f mb (QΣ Σ).
  Proof using TOPH.
    intros Σ F fc mb xbs xlen jt CTX XA XL XN LEN ZR TBLK. unfold nd_a_mset_k. intros until mm. intros SPILL TSH MI MU WM H7.
    pose proof ((T1 top_ctx_stepA) Σ 0%Z fc mb mm CTX MU WM) as CTXm. pose proof CTXm as (SR & HU & FRM & ARTm & MRm & PKm).
    pose proof PKm as (_ & _ & _ & _ & ST). top_env Σ SR.
    transport_after_call bsegs mb mm MU WM. clear CTX MU WM.
    apply evt_done.
    assert (JL : length jt = 504%nat) by exact (proj1 (proj1 (proj1 TBLK))).
    pose proof (u8arr_of_rw_cells bsegs mm _ _ _ TBLK) as TA5. clear TBLK.
    assert (ZRT : bytes_at bsegs mm ((f + 32) / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63))
      by (replace ((f + 32) / 8 + 2147450880)%Z with (f / 8 + 2147450884)%Z by lia; exact (zero_run_of_CB mm _ 63 TSH)).
    assert (TFR : exists f0 c, In (f0, c) (rt_frames RT Σ) /\ (f0 <= f + 32)%Z /\ (f + 32 + Z.of_nat (length jt) <= f0 + fs_size c - 8)%Z)
      by (exists f, 4%nat; split; [exact HinF| rewrite JL; lia]).
    eapply (aevt_memset_u8 RT AF RTF PMc FDO MST Σ K mm (f + 32)%Z jt 63 lo (Z_to_bv 64 spq) TA5 ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(rewrite JL; lia) ltac:(rewrite JL; lia)
              ltac:(rewrite JL; lia) ZRT TFR ARTm MI ((T1 top_cok) Σ 0%Z mm SR ST)) with (dz := 8%Z) (nz := 496%Z) (cb := Z_to_bv 8 0);
      [f_equal; lia | reflexivity | reflexivity | lia | lia | rewrite JL; lia | lia | exact FRM | ].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' tbs5 FRM' RA PRX TA5' TL5'.
    rewrite ?unsigned_lit in RA, PRX by lia.
    pose proof ((T1 nd_ctx_call) Σ 0%Z fc fc' mm m' _ _ CTXm FRM' RA PRX ltac:(left; lia)) as CTX'.
    destruct RA as (ART' & MI' & WM' & ST').
    pose proof (agree_of_pres_ex _ _ _ _ _ mm m' _ PRX (fun x H => H)) as AG.
    clear TA5 ST MI ZRT. unfold nd_spill in SPILL. nd_after_call mm m' AG WM'.

    pose proof (rw_cells_of_u8arr bsegs m' _ _ TA5') as TC. rewrite TL5', JL in TC.
    apply (rw_cells_split_CB bsegs m' _ [] 504 tbs5 [] [496; 2; 6]%nat) in TC; [| reflexivity]. cbn [mk_CB_cells app] in TC.
    repeat match goal with H : rw_cells _ _ _ ?l |- _ => match l with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in H; clearbody j end end.
    destruct (proj1 (num_rw_cells_app bsegs _ _ [CB 496 _] _) TC) as [TAc TC1]. clear TC. cbn [cells_size csize Nat.add] in TC1. change (Z.of_nat 496) with 496%Z in TC1.
    destruct (proj1 (num_rw_cells_app bsegs _ _ [CB 2 _] _) TC1) as [TNc _]. clear TC1.
    replace (f + 32 + 496)%Z with (f + 528)%Z in TNc by lia.
    lazymatch type of TAc with rw_cells _ _ _ [CB _ ?jj] => assert (TL' : length jj = 496%nat) by exact (proj1 (proj1 (proj1 TAc))) end.
    pose proof (u8arr_of_rw_cells bsegs m' _ _ _ TAc) as TA'. clear TAc.
    apply (aevt_evt RT AF PMc MST). num_ret_pc.
    eapply evt_eq; [| eapply (EVA nd_288 F' fc' m' (QΣ Σ) (nd_kp5 Σ F' fc' m' CTX') ((T1 nd_kshlt) Σ 0%Z F' fc' m' CTX') ((T1 nd_kshlx) Σ 0%Z F' fc' m' CTX') ((T1 nd_k55c) Σ 0%Z F' fc' m' CTX') t7);
                        [unfold nd_spill; exact SPILL | exact XA | exact XL | exact XN | exact LEN | exact ZR | exact TA' | exact TL' | exact TNc | exact TSH | exact MI'
                        | apply munch_refl | apply wmono_refl | exact H7]].
    num_st_eq.
  Qed.

  Lemma nd_body : forall Σ F fc mb xbs xlen jt xra xt0 xt1 xt2 xa6 xa7 xs2 xs5 xs8 xs11 xt3 xt4 xt5 xt6 c0 c8 c16 c24 c32 c40 c48 jz,
    nd_ctx Σ 0 fc mb ->
    u8arr bsegs mb X xbs -> length xbs = 496%nat -> rw_cells bsegs mb (X + 496) [C2 (Z_to_bv 64 xlen)] -> (0 <= xlen <= 62)%Z ->
    bytes_at bsegs mb (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) -> rw_cells bsegs mb (f + 32) [CB 504 jt] ->
    rw_cells bsegs mb spq [C8 c0; C8 c8; C8 c16; C8 c24; C8 c32; C8 c40; C8 c48] ->
    rw_cells bsegs mb (f / 8 + 2147450884) [CB 63 jz] -> mem_inv bsegs mb ->
    aevt RT PMc Σ K
      (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) (Z_to_bv 64 f) (Z_to_bv 64 (-13)) (Z_to_bv 64 p2) (Z_to_bv 64 107384) (Z_to_bv 64 1028088) (Z_to_bv 64 (-8)) xa6 xa7
               xs2 (Z_to_bv 64 S) (Z_to_bv 64 (p2 mod 4294967296)) xs5 (Z_to_bv 64 X) (Z_to_bv 64 (- e)) xs8 (Z_to_bv 64 f) (Z_to_bv 64 2147450880) xs11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0xfb214) fc None mb (seg_rom bsegs)).
  Proof using TOPH.
    intros until jz. intros CTX XA XL XN LEN ZR TBLK SPILL TSH MI.
    apply (aevt_evt RT AF PMc MST).
    eapply (EVAa nd_a F fc mb (QΣ Σ) (nd_kms Σ F fc mb xbs xlen jt CTX XA XL XN LEN ZR TBLK));
      [exact SPILL | exact TSH | exact MI | apply munch_refl | apply wmono_refl].
  Qed.
End NDTOP3.

Theorem ndcb_ok : forall RT, art_facts RT -> rt_contracts_f RT ->
  forall PMc, fdfs_only PMc -> mat_stable PMc -> p5b_stmt RT PMc -> ndcb_stmt RT PMc.
Proof.
  intros RT AF RTF PMc FDO MST HP5. unfold ndcb_stmt.
  intros Σ K ra sp gp tp t0 t1 t2 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m X p2 e cr lo
    ETP FRM FRL HE HCR HER CRD PR ART0 MI ST LOR ROOM TOP SP16 AB HK.
  destruct (abig_elim RT _ _ _ AB) as (bs & n & RAW).
  pose proof (abig_facts RT AF Σ m X bs n lo ART0 LOR RAW) as XNUM. pose proof XNUM as (XN0 & XN1 & XN2 & XN3 & XN4).
  destruct RAW as (XA & XL & XN & LEN & ZR & X8 & (g & kg & XG)).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof ROOM as ROOM'. pose proof TOP as TOP'. unfold NDCB_STACK, P5B_STACK, LMB_STACK, RT_STACK, USTACK_TOP in ROOM', TOP'.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. unfold SEGTOP_A, STACK_WIN, USTACK_TOP in SP0R. pose proof LOR as LOR'. unfold STACK_WIN in LOR'.
  pose proof (repeat_length (Z_to_bv 8 0) 63) as RL.
  apply (aevt_evt RT AF PMc MST).
  eapply (nd_pro1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m ROOM TOP SP16 ltac:(lia) _ (Z_to_bv 64 X) a1 (Z_to_bv 64 (p2 mod 4294967296)) (Z_to_bv 64 (- e)));
    [| exact MI | exact ST | exact (af_client_consts RT AF Σ m ART0)].

  intros d spq xt0 xt1 xt2 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 mm REAL MI1 MU1 WM1 ST1.
  destruct REAL as (Hd & Hspq & (jsp & SPILLc) & (jh & HIGHc) & SAVED).
  apply evt_done.
  apply (u8arr_transport bsegs [((bv_unsigned sp - 176)%Z, bv_unsigned sp)] m mm X bs) in XA; [| exact MU1 | exact WM1 | cbn [disjoint_from]; split; [lia| exact I]].
  apply (rw_cells_transport bsegs [((bv_unsigned sp - 176)%Z, bv_unsigned sp)] m mm) in XN; [| exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Nat.add]; split; [lia| exact I]].
  apply (bytes_at_transport bsegs [((bv_unsigned sp - 176)%Z, bv_unsigned sp)] m mm) in ZR; [| exact MU1 | cbn [disjoint_from]; split; [lia| exact I]].
  assert (FP1 : fp_ok RT Σ lo [((bv_unsigned sp - 176)%Z, bv_unsigned sp)]) by (constructor; [left; cbn [fst snd]; unfold USTACK_TOP; lia| constructor]).
  pose proof (art_of_munch RT AF Σ m mm lo _ ART0 LOR FP1 MU1 WM1) as ART1.
  assert (COK : call_ok RT Σ mm (Z_to_bv 64 spq) lo).
  { unfold call_ok. rewrite unsigned_lit by lia. split; [exact ST1|]. split; [exact LOR|]. unfold RT_STACK, USTACK_TOP.
    split; [lia|]. split; [lia| Z.div_mod_to_equations; lia]. }
  eapply (aevt_stack_malloc RT RTF PMc FDO MST Σ K 4%nat); [left; reflexivity | exact ETP | unfold FRAMES_MAX in *; lia | lia | exact ART1 | exact MI1 | exact COK | intros Efr0; exfalso; pose proof (proj1 XG) as XIN; rewrite Efr0 in XIN; exact XIN | exact FRM |].
  intros Σ' f q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' m' FRM' RA PRA W1 W2 EF EL ES EC F0 F64 FTOP.
  rewrite ?unsigned_lit in RA, PRA by lia. destruct RA as (ART' & MI' & WM' & ST').

  pose proof (agree_pres _ _ _ mm m' (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) spq x) PRA (fun x H => H)) as AG.
  unfold LM_SAVED in SAVED. pose proof (proj1 XG) as HinG0. destruct XG as (_ & G1 & G2).
  rt_transport_with mm m' AG WM' ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?repeat_length, ?XL in Hx; cbv beta; aclient_tac).

  assert (MREL : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(X, (X + 504)%Z)] m m').
  { eapply pres_fp_trans.
    - apply (pres_fp_of_munch _ _ _ _ _ _ _ MU1). intros a Ha _. pose proof (aclient_split_c RT AF Σ m _ a ART0 Ha) as SPL.
      cbn [outside]. split; [lia| exact I].
    - intros a Ha _. apply PRA. eapply aclient_mono; [exact Ha| auto| auto| lia]. }
  assert (MRb : nd_mrel RT Σ sp X m m') by (split; [exact (wmono_trans bsegs _ _ _ WM1 WM')| exact MREL]).

  assert (HinF : In (f, 4%nat) (rt_frames RT Σ')) by (rewrite EF; left; reflexivity).
  pose proof (new_frame_facts RT AF Σ' m' f 4 1016 lo ART' ltac:(rewrite ES; exact LOR) HinF eq_refl eq_refl ltac:(lia)) as NF.
  change (1016 / 8)%Z with 127%Z in NF.
  pose proof (frames_sep RT AF Σ' m' f 4 (rt_frames RT Σ) X 504 ART' EF X8 ltac:(lia) eq_refl ltac:(exists g, kg; split; [exact HinG0| lia])) as SEP.
  cbv zeta in SEP. change (fs_size 4) with 1024%Z in SEP. change (1024 / 8)%Z with 128%Z in SEP. change (504 / 8)%Z with 63%Z in SEP.
  change (fs_size 4 - 8)%Z with 1016%Z in W1. change (fs_size 4 / 8)%Z with 128%Z in W2. unfold shad, SHB in W2.
  destruct (wr_at_rw_CB m' f 1016 W1 ltac:(lia)) as [jf FRD]. destruct (wr_at_rw_CB m' _ 128 W2 ltac:(lia)) as [js FRS].
  change (Z.to_nat 1016) with 1016%nat in FRD. change (Z.to_nat 128) with 128%nat in FRS.
  apply (rw_cells_split_CB bsegs m' f [] 1016 jf [] [32; 504; 480]%nat) in FRD; [| reflexivity]. cbn [mk_CB_cells app] in FRD.
  destruct (proj1 (num_rw_cells_app bsegs _ _ [CB 32 _] _) FRD) as [HDR0 FD1]. clear FRD.
  cbn [cells_size csize Nat.add] in FD1. change (Z.of_nat 32) with 32%Z in FD1.
  destruct (proj1 (num_rw_cells_app bsegs _ _ [CB 504 _] _) FD1) as [TBLK _]. clear FD1.
  apply (rw_cells_split_CB bsegs m' f [] 32 _ [] [8;8;8;8]%nat) in HDR0; [| reflexivity]. cbn [app] in HDR0. rewrite app_nil_r in HDR0.
  apply (rw_cells_split_CB bsegs m' _ [] 128 js [] [4; 72; 52]%nat) in FRS; [| reflexivity]. cbn [mk_CB_cells app] in FRS.
  destruct (proj1 (num_rw_cells_app bsegs _ _ [CB 4 _] _) FRS) as [S0 FRS1]. clear FRS. cbn [cells_size csize Nat.add] in FRS1. change (Z.of_nat 4) with 4%Z in FRS1.
  destruct (proj1 (num_rw_cells_app bsegs _ _ [CB 72 _] _) FRS1) as [SZ _]. clear FRS1.
  replace (f / 8 + 2147450880 + 4)%Z with (f / 8 + 2147450884)%Z in SZ by lia.
  destruct NF as (NF1 & NF2 & NF3 & NF4 & NF5 & NF6).

  apply (aevt_evt RT AF PMc MST).
  replace (ret_pc (Z_to_bv 64 1028212)) with (Z_to_bv 64 1028212) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  eapply (nd_poison f p2 m' NF1 ltac:(lia) NF4 ltac:(lia) PR _); [| exact HDR0 | exact S0 | exact SZ | exact MI' | apply munch_refl | apply wmono_refl].
  intros h' jz' mm2 HDR2 SHZ2 MI2 MU2 WM2.
  apply evt_done.
  destruct SEP as (SEP1 & SEP2 & SEP3 & SEP4).
  clear HDR0 S0 SZ MI' AG.
  transport_after_call bsegs m' mm2 MU2 WM2.
  apply (rw_cells_split_CB bsegs mm2 _ [] 72 jz' [] [63; 9]%nat) in SHZ2; [| reflexivity]. cbn [mk_CB_cells app] in SHZ2.
  destruct (proj1 (num_rw_cells_app bsegs _ _ [CB 63 _] _) SHZ2) as [SHZ3 _]. clear SHZ2.

  assert (SR : Sj_num_nd_top.nd_srel RT Σ f Σ' 0) by (unfold Sj_num_nd_top.nd_srel; repeat split; try assumption; lia).
  assert (SPQ : ((d = 0 \/ d = 16) /\ spq = bv_unsigned sp - 160 - d)%Z) by (split; [exact Hd| lia]).
  assert (NF : (f mod 64 = 0 /\ 0x6e0000 <= f /\ f + 1016 <= lo /\ (f + 1016 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 127 <= f) /\ 0 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 127 <= lo)%Z)
    by (repeat split; assumption).
  assert (XG : In (g, kg) (rt_frames RT Σ) /\ (g <= X)%Z /\ (X + 504 <= g + fs_size kg - 8)%Z) by (repeat split; assumption).
  assert (SEP : ((X + 504 <= f \/ f + 1024 <= X) /\ (X + 504 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 128 <= X)
                    /\ (X / 8 + 2147450880 + 63 <= f \/ f + 1024 <= X / 8 + 2147450880)
                    /\ (X / 8 + 2147450880 + 63 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 128 <= X / 8 + 2147450880))%Z) by (repeat split; assumption).
  assert (HW2 : tk_wf sp X lo f [(f, (f + 32)%Z); ((f / 8 + 2147450880)%Z, (f / 8 + 2147450880 + 76)%Z)])
    by (unfold tk_wf; constructor; [right; left; cbn [fst snd]; lia|]; constructor; [right; right; left; cbn [fst snd]; lia| constructor]).
  assert (CTX : Sj_num_nd_top.nd_ctx RT Σ ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X lo d spq f m cr Σ' 0 fc' mm2).
  { split; [exact SR|]. split; [lia|]. split; [exact FRM'|].
    split; [exact (art_of_munch RT AF Σ' m' mm2 lo _ ART' ltac:(rewrite ES; exact LOR)
                     (tk_fpok RT AF Σ Σ' sp X lo d spq f g kg ROOM TOP LOR EF EL ES SPQ NF X8 XG XNUM SEP _ HW2) MU2 WM2)|].
    split; [exact (nd_mrel_munch RT AF Σ Σ' sp X lo d spq f g kg m ROOM TOP LOR EF EL ES SPQ NF X8 XG XNUM SEP _ m' mm2 HW2 ART' MRb MU2 WM2)|].
    split; [exists jh; exact HIGHc|]. split; [exact SAVED|]. split; [exists h'; exact HDR2|].
    split; [exact W2| exact ST']. }

  apply (rw_cells_split_CB bsegs mm2 _ [] 56 jsp [] [8;8;8;8;8;8;8]%nat) in SPILLc; [| reflexivity]. cbn [mk_CB_cells app] in SPILLc.
  repeat match goal with H : rw_cells _ _ _ ?l |- _ => match l with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in H; clearbody j end end.
  repeat lazymatch type of SPILLc with
  | rw_cells _ _ _ ?l =>
      lazymatch l with
      | context [CB 8 ?bsx] =>
          let pre := lazymatch l with
                     | CB 8 bsx :: _ => constr:(@nil cell)
                     | ?c1 :: CB 8 bsx :: _ => constr:([c1])
                     | ?c1 :: ?c2 :: CB 8 bsx :: _ => constr:([c1; c2])
                     | ?c1 :: ?c2 :: ?c3 :: CB 8 bsx :: _ => constr:([c1; c2; c3])
                     | ?c1 :: ?c2 :: ?c3 :: ?c4 :: CB 8 bsx :: _ => constr:([c1; c2; c3; c4])
                     | ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: CB 8 bsx :: _ => constr:([c1; c2; c3; c4; c5])
                     | ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: CB 8 bsx :: _ => constr:([c1; c2; c3; c4; c5; c6])
                     end in
          apply (num_cb8_c8 bsegs _ _ pre _ bsx) in SPILLc; cbn [app] in SPILLc
      end
  end.
  lazymatch type of TBLK with rw_cells _ _ _ [CB 504 ?jt] =>
    eapply (nd_body RT AF RTF PMc FDO MST HP5 Σ K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X lo d spq f g kg m p2 e cr
              ETP ROOM TOP SP16 LOR FRL HE HCR HER CRD PR SPQ NF X8 XG XNUM SEP HK Σ' F' fc' mm2 bs n jt);
      [exact CTX | exact XA | exact XL | exact XN | exact LEN | exact ZR | exact TBLK | exact SPILLc | exact SHZ3 | exact MI2]
  end.
Qed.
