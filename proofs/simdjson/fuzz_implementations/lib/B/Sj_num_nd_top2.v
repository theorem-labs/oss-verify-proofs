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
  Sj_num_lm_pro Sj_num_lm_kit Sj_num_nd_pro Sj_num_nd_defs Sj_num_nd_a Sj_num_nd_b3 Sj_num_nd_tkit Sj_num_nd_top.
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

Section NDTOP2.
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

  Lemma top_bbig_t : forall Σ used (mm : mem) tbs tlen, nd_srel Σ used ->
    u8arr bsegs mm (f + 32) tbs -> length tbs = 496%nat -> rw_cells bsegs mm (f + 528) [C2 (Z_to_bv 64 tlen)] -> (0 <= tlen <= 62)%Z ->
    rw_cells bsegs mm (f / 8 + 2147450884) [CB 63 (repeat (Z_to_bv 8 0) 63)] -> bbig RT Σ mm (f + 32) tbs tlen.
  Proof using TOPH.
    intros Σ used mm tbs tlen SR TA TL TN TLN TSH. top_env Σ SR.
    pose proof (abig_intro RT Σ mm (f + 32) tbs tlen) as AI. unfold abig_raw in AI.
    assert (AB : abig RT Σ mm (f + 32)).
    { apply AI. split; [exact TA|]. split; [exact TL|]. split; [replace (f + 32 + 496)%Z with (f + 528)%Z by lia; exact TN|]. split; [lia|].
      split; [replace ((f + 32) / 8 + 2147450880)%Z with (f / 8 + 2147450884)%Z by lia; exact (zero_run_of_CB mm _ 63 TSH)|].
      split; [Z.div_mod_to_equations; lia|]. exists f, 4%nat. split; [exact HinF| lia]. }
    destruct AB as (FO & _ & _). split; [exact FO|]. split; [exact TL|]. split; [exact TA|]. split; [replace (f + 32 + 496)%Z with (f + 528)%Z by lia; exact TN| lia].
  Qed.
  Lemma top_bbig_x : forall Σ used (mm : mem) xbs xlen, nd_srel Σ used ->
    u8arr bsegs mm X xbs -> length xbs = 496%nat -> rw_cells bsegs mm (X + 496) [C2 (Z_to_bv 64 xlen)] -> (0 <= xlen <= 62)%Z ->
    bytes_at bsegs mm (X / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63) -> bbig RT Σ mm X xbs xlen.
  Proof using TOPH.
    intros Σ used mm xbs xlen SR XA XL XN LEN ZR. top_env Σ SR.
    pose proof (abig_intro RT Σ mm X xbs xlen) as AI. unfold abig_raw in AI.
    assert (AB : abig RT Σ mm X).
    { apply AI. split; [exact XA|]. split; [exact XL|]. split; [exact XN|]. split; [exact LEN|]. split; [exact ZR|]. split; [exact X8|].
      exists g, kg. split; [exact HinG| split; [exact G1| exact G2]]. }
    destruct AB as (FO & _ & _). split; [exact FO|]. split; [exact XL|]. split; [exact XA|]. split; [exact XN| exact LEN].
  Qed.

  Lemma nd_kshlt : forall Σ used F fc mb, nd_ctx Σ used fc mb -> nd_shlt_k sp gp tp F fc X p2 e spq f mb (QΣ Σ).
  Proof using TOPH.
    intros Σ used F fc mb CTX. unfold nd_shlt_k. intros until tlen. intros INV Hn. nd_site INV CTX.
    pose proof SR as (EF & EL & ES & EC).
    apply evt_done.
    pose proof (top_bbig_t Σ used mm tbs tlen SR TA TL TN TLN TSH) as BBT.
    eapply (shlb_ok RT AF RTF PMc FDO MST Σ) with (X := (f + 32)%Z) (n := n) (lo := lo) (bs := tbs) (len := tlen); rewrite ?unsigned_lit by lia; unfold SHLB_STACK, RT_STACK, USTACK_TOP;
      [ exact ETP | exact FRM | lia | exact ARTm | exact MI | exact ST | exact ((T1 top_lor1) Σ used SR) | lia | lia | Z.div_mod_to_equations; lia | exact BBT | ].
    intros Σ' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' bs' len' FRM' RA PRF BB' _ EF' EL' ES' EC'.
    rewrite ?unsigned_lit in RA, PRF by lia.
    assert (SR' : nd_srel Σ' used) by (unfold nd_srel; rewrite EF', EL', ES'; repeat split; try assumption; lia).
    assert (PRX : rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) spq (f + 32) 504 mm m').
    { intros a Ha Hda. apply PRF; [exact Ha|]. cbn [outside]. split; [lia| exact I]. }
    pose proof ((T1 nd_ctx_call2) Σ Σ' used used fc fc' mm m' _ _ CTXm SR' HU FRM' RA PRX ltac:(left; lia)) as CTX'.
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
    eapply evt_eq; [| eapply (EVA nd_2cc F' fc' m' (QΣ Σ') ((T1 nd_k55c) Σ' used F' fc' m' CTX')); exact INV'].
    num_st_eq.
  Qed.

  Lemma nd_kshlx : forall Σ used F fc mb, nd_ctx Σ used fc mb -> nd_shlx_k sp gp tp F fc X p2 e spq f mb (QΣ Σ).
  Proof using TOPH.
    intros Σ used F fc mb CTX. unfold nd_shlx_k. intros until tlen. intros INV Hn. nd_site INV CTX.
    pose proof SR as (EF & EL & ES & EC).
    apply evt_done.
    pose proof (top_bbig_x Σ used mm xbs xlen SR XA XL XN LEN ZR) as BBX.
    eapply (shlb_ok RT AF RTF PMc FDO MST Σ) with (X := X) (n := n) (lo := lo) (bs := xbs) (len := xlen); rewrite ?unsigned_lit by lia; unfold SHLB_STACK, RT_STACK, USTACK_TOP;
      [ exact ETP | exact FRM | lia | exact ARTm | exact MI | exact ST | exact ((T1 top_lor1) Σ used SR) | lia | lia | Z.div_mod_to_equations; lia | exact BBX | ].
    intros Σ' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' bs' len' FRM' RA PRF BB' _ EF' EL' ES' EC'.
    rewrite ?unsigned_lit in RA, PRF by lia.
    assert (SR' : nd_srel Σ' used) by (unfold nd_srel; rewrite EF', EL', ES'; repeat split; try assumption; lia).
    assert (PRX : rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) spq X 504 mm m').
    { intros a Ha Hda. apply PRF; [exact Ha|]. cbn [outside]. split; [lia| exact I]. }
    pose proof ((T1 nd_ctx_call2) Σ Σ' used used fc fc' mm m' _ _ CTXm SR' HU FRM' RA PRX ltac:(right; lia)) as CTX'.
    destruct RA as (ART' & MI' & WM' & ST').
    destruct BB' as (_ & XL' & XA' & XN' & LEN').
    pose proof (agree_of_pres_ex _ _ _ _ _ mm m' (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) spq x /\ ~ (X <= x < X + 504)%Z) PRX (fun x H => H)) as AG.
    clear XA XN ST MI BBX. nd_after_call mm m' AG WM'.
    assert (INV' : nd_inv X spq f m' (repeat (Z_to_bv 8 0) 63) m' len' tlen).
    { unfold nd_inv, nd_spill. split; [exists c0, c8, c16, c32, c40; exact SPILL|]. split; [exists bs'; split; [exact XA'| exact XL']|].
      split; [exact XN'|]. split; [lia|]. split; [exact ZR|]. split; [exists tbs; split; [exact TA| exact TL]|].
      split; [exact TN|]. split; [lia|]. split; [exact TSH|]. split; [exact MI'|]. split; [apply munch_refl| apply wmono_refl]. }
    apply (aevt_evt RT AF PMc MST). num_ret_pc.
    eapply evt_eq; [| eapply (EVA nd_2cc F' fc' m' (QΣ Σ') ((T1 nd_k55c) Σ' used F' fc' m' CTX')); exact INV'].
    num_st_eq.
  Qed.

End NDTOP2.
