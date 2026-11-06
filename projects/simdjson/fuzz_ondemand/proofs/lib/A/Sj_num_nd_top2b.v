(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx I_lkit Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_abig Sj_num_acall Sj_num_acall2 Sj_num_aframe Sj_num_lm_pro
  Sj_num_lm_kit Sj_num_nd_defs Sj_num_nd_tkit Sj_num_nd_pro Sj_num_nd_a Sj_num_nd_b Sj_num_nd_rel Sj_num_nd_c Sj_num_nd_d Sj_num_nd_top.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_zc_hook | asan_zcp_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section NDTOP.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RTF : rt_contracts_f RT.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.
  Hypothesis HP5 : p5a_stmt RT PMc.

  Variables (Σ0 : rts RT) (K : config -> Prop).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (X lo d spq f g : Z) (kg : nat) (me : mem) (e cr : Z).
  Notation SP := (bv_unsigned sp).
  Notation S := (f / 8 + 2147450880)%Z.
  Hypothesis ETP : tp = Z_to_bv 64 0x6488f0.
  Hypothesis ROOM : (lo + NDCA_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis LOR : (rt_sp0 RT Σ0 - STACK_WIN <= lo)%Z.
  Hypothesis FRL : (length (rt_frames RT Σ0) + 2 <= FRAMES_MAX)%nat.
  Hypothesis HE : (0 <= e < 135 * (cr + 1))%Z.
  Hypothesis HCR : (0 <= cr)%Z.
  Hypothesis HE31 : (e < 2147483648)%Z.
  Hypothesis CRD : (cr + 1 <= rt_credit RT Σ0)%Z.
  Hypothesis SPQ : ((d = 0 \/ d = 16) /\ spq = SP - 160 - d)%Z.
  Hypothesis NF : (f mod 64 = 0 /\ 0x66b000 <= f /\ f + 1016 <= lo /\ (f + 1016 <= S \/ S + 127 <= f) /\ 0 <= S /\ S + 127 <= lo)%Z.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis XG : In (g, kg) (rt_frames RT Σ0) /\ (g <= X)%Z /\ (X + 504 <= g + fs_size kg - 8)%Z.
  Hypothesis XNUM : (0x66b000 <= X /\ X + 504 <= lo /\ (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)
                     /\ 0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo)%Z.
  Hypothesis SEP : ((X + 504 <= f \/ f + 1024 <= X) /\ (X + 504 <= S \/ S + 128 <= X)
                    /\ (X / 8 + 2147450880 + 63 <= f \/ f + 1024 <= X / 8 + 2147450880)
                    /\ (X / 8 + 2147450880 + 63 <= S \/ S + 128 <= X / 8 + 2147450880))%Z.

  Hypothesis HK : forall (Σ' : rts RT) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m', frm0 fc' ->
     rt_after RT Σ' SP lo me m' -> rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) SP [(X, X + 504)%Z] me m' ->
     abig RT Σ' m' X ->
     rt_frames RT Σ' = rt_frames RT Σ0 -> rt_live RT Σ' = rt_live RT Σ0 -> rt_sp0 RT Σ' = rt_sp0 RT Σ0 ->
     (rt_credit RT Σ0 - (cr + 1) <= rt_credit RT Σ')%Z ->
     aevt RT PMc Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F' (ret_pc ra) fc' None m' (seg_rom asegs)).
  Collection TOPH := AF RTF FDO MST HP5 ETP ROOM TOP SP16 LOR FRL HE HCR HE31 CRD SPQ NF X8 XG XNUM SEP HK.

  Notation MREL := (nd_mrel RT Σ0 sp X me).
  Notation PARK := (nd_park ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo d spq f).
  Notation NDS F fc pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs3 (Z_to_bv 64 S) xs5 xs6 xs7 xs8 xs9
             (Z_to_bv 64 f) (Z_to_bv 64 2147450880) xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Notation T1 L := (L RT AF RTF PMc FDO MST HP5 Σ0 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X lo d spq f g kg me e cr
                      ETP ROOM TOP SP16 LOR FRL HE HCR HE31 CRD SPQ NF X8 XG XNUM SEP HK) (only parsing).
  Notation nd_srel := (Sj_num_nd_top.nd_srel RT Σ0 f).
  Notation nd_ctx := (Sj_num_nd_top.nd_ctx RT Σ0 ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X lo d spq f me cr).
  Notation EVA L F fc mb := (L sp gp tp F fc X lo d spq f mb (T1 top_spq) ROOM TOP (proj1 NF) (conj (proj1 (proj2 NF)) (proj1 (proj2 (proj2 NF))))
                               (proj1 (proj2 (proj2 (proj2 NF)))) (proj2 (proj2 (proj2 (proj2 NF)))) X8
                               (conj (proj1 XNUM) (proj1 (proj2 XNUM))) (proj1 (proj2 (proj2 XNUM))) (proj2 (proj2 (proj2 XNUM))) SEP) (only parsing).
  Ltac top_env Σ SR :=
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof NF as (N1 & N2 & N3 & N4 & N5 & N6); pose proof XNUM as (Q1 & Q2 & Q3 & Q4 & Q5); pose proof SEP as (E1 & E2 & E3 & E4);
    pose proof (T1 top_spq) as [Hd Hs]; pose proof ROOM as ROOM'; pose proof TOP as TOP'; unfold NDCA_STACK, P5A_STACK, LMA_STACK, RT_STACK, USTACK_TOP in ROOM', TOP';
    pose proof (T1 top_inF Σ _ SR) as HinF; pose proof (f64_8 f (proj1 NF)) as F8; pose proof (eq_refl : fs_size 4 = 1024%Z) as FS4;
    pose proof (proj1 (proj2 XG)) as G1; pose proof (proj2 (proj2 XG)) as G2; pose proof (T1 top_inG Σ _ SR) as HinG;
    pose proof (repeat_length (Z_to_bv 8 0) 63) as RL;
    assert (F32 : ((f + 32) / 8 = f / 8 + 4)%Z) by (replace (f + 32)%Z with (f + 8 * 4)%Z by lia; apply f64_div; exact (proj1 NF)).

  Ltac nd_site INV CTX :=
    pose proof INV as ((c0 & c8 & c24 & c32 & c40 & c48 & SPILL) & (xbs & XA & XL) & XN & LEN & ZR & (tbs & TA & TL) & TN & TLN & TSH & MI & MU & WM);
    unfold nd_W in MU;
    lazymatch type of CTX with Sj_num_nd_top.nd_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?Σ ?used ?fc ?mb =>
      lazymatch type of MU with munch _ _ ?mm =>
        pose proof (T1 top_ctx_step Σ used fc mb mm CTX MU WM) as CTXm; pose proof CTXm as (SR & HU & FRM & ARTm & MRm & PKm);
        pose proof PKm as (_ & _ & _ & _ & ST); top_env Σ SR; clear CTX MU WM INV
      end end.

  Notation QΣ Σ := (fun ms' => aevt RT PMc Σ K ms').
  Ltac nd_after_call mm m' PR WM' :=
    let AG := fresh "AG" in
    pose proof (agree_of_pres_ex _ _ _ _ _ mm m' _ PR (fun x H => H)) as AG;
    rt_transport_with mm m' AG WM' ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?repeat_length in Hx; repeat match goal with HL : length _ = 496%nat |- _ => progress (rewrite HL in Hx) end; cbv beta; split; [aclient_tac| lia]).
  Ltac nd_inv_at m' :=
    pose proof (munch_refl (nd_W X spq f) m') as MU1; pose proof (wmono_refl asegs m') as WM1;
    unfold nd_inv; split; [do 6 eexists; eassumption|]; split; [eexists; split; [eassumption| lia]|];
    split; [eassumption|]; split; [lia|]; split; [eassumption|]; split; [eexists; split; [eassumption| lia]|];
    split; [eassumption|]; split; [lia|]; split; [eassumption|]; split; [eassumption|]; split; [exact MU1| exact WM1].

  Lemma nd_kmsx : forall Σ used F fc mb, nd_ctx Σ used fc mb -> nd_msx_k sp gp tp F fc X spq f mb (QΣ Σ).
  Proof using TOPH.
    intros Σ used F fc mb CTX. unfold nd_msx_k. intros until mm. intros INV Hk Hn Hkn. nd_site INV CTX.
    assert (ZRT : bytes_at asegs mm ((f + 32) / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63))
      by (replace ((f + 32) / 8 + 2147450880)%Z with (f / 8 + 2147450884)%Z by lia; exact (zero_run_of_CB mm _ 63 TSH)).
    assert (TFR : exists f0 c, In (f0, c) (rt_frames RT Σ) /\ (f0 <= f + 32)%Z /\ (f + 32 + Z.of_nat (length tbs) <= f0 + fs_size c - 8)%Z)
      by (exists f, 4%nat; split; [exact HinF| rewrite TL; lia]).
    assert (XFR : exists f0 c, In (f0, c) (rt_frames RT Σ) /\ (f0 <= X)%Z /\ (X + Z.of_nat (length xbs) <= f0 + fs_size c - 8)%Z)
      by (exists g, kg; split; [exact HinG| rewrite XL; lia]).
    apply evt_done.
    eapply (aevt_memset_u8 RT AF RTF PMc FDO MST Σ K mm X xbs 63 lo (Z_to_bv 64 spq) XA X8 ltac:(lia) ltac:(rewrite XL; lia) ltac:(rewrite XL; lia)
              ltac:(rewrite XL; lia) ZR XFR ARTm MI (T1 top_cok Σ used mm SR ST)) with (dz := 0%Z) (nz := (8 * k)%Z) (cb := Z_to_bv 8 0);
      [f_equal; lia | reflexivity | reflexivity | lia | lia | rewrite XL; lia | lia | exact FRM | ].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' xbs' FRM' RA PR XA' XL'.
    rewrite ?unsigned_lit in RA, PR by lia.
    pose proof (T1 nd_ctx_call Σ used fc fc' mm m' _ _ CTXm FRM' RA PR ltac:(right; lia)) as CTX'.
    destruct RA as (ART' & MI' & WM' & ST').
    clear XA ST MI ZRT. nd_after_call mm m' PR WM'.
    assert (INV' : nd_inv X spq f m' (repeat (Z_to_bv 8 0) 63) (Z_to_bv 64 (8 * k)) m' n tlen) by nd_inv_at m'.
    apply (aevt_evt RT AF PMc MST). num_ret_pc.
    eapply evt_eq; [| eapply (EVA nd_300 F' fc' m' (QΣ Σ) (T1 nd_k564 Σ used F' fc' m' CTX') k n tlen); [exact INV' | lia | lia | lia]].
    num_st_eq.
  Qed.

  Lemma nd_kmvx : forall Σ used F fc mb, nd_ctx Σ used fc mb -> nd_mvx_k sp gp tp F fc X spq f mb (QΣ Σ).
  Proof using TOPH.
    intros Σ used F fc mb CTX. unfold nd_mvx_k. intros until mm. intros INV Hk Hn Hkn. nd_site INV CTX.
    assert (ZRT : bytes_at asegs mm ((f + 32) / 8 + 2147450880) (repeat (Z_to_bv 8 0) 63))
      by (replace ((f + 32) / 8 + 2147450880)%Z with (f / 8 + 2147450884)%Z by lia; exact (zero_run_of_CB mm _ 63 TSH)).
    assert (TFR : exists f0 c, In (f0, c) (rt_frames RT Σ) /\ (f0 <= f + 32)%Z /\ (f + 32 + Z.of_nat (length tbs) <= f0 + fs_size c - 8)%Z)
      by (exists f, 4%nat; split; [exact HinF| rewrite TL; lia]).
    assert (XFR : exists f0 c, In (f0, c) (rt_frames RT Σ) /\ (f0 <= X)%Z /\ (X + Z.of_nat (length xbs) <= f0 + fs_size c - 8)%Z)
      by (exists g, kg; split; [exact HinG| rewrite XL; lia]).
    apply evt_done.
    eapply (aevt_memmove_u8 RT AF RTF PMc FDO MST Σ K mm X xbs 63 lo (Z_to_bv 64 spq) XA X8 ltac:(lia) ltac:(rewrite XL; lia) ltac:(rewrite XL; lia)
              ltac:(rewrite XL; lia) ZR XFR ARTm MI (T1 top_cok Σ used mm SR ST)) with (dz := (8 * k)%Z) (sz := 0%Z) (nz := (8 * n)%Z);
      [reflexivity | f_equal; lia | reflexivity | lia | lia | lia | rewrite XL; lia | rewrite XL; lia | lia | exact FRM | ].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' xbs' FRM' RA PR XA' XL'.
    rewrite ?unsigned_lit in RA, PR by lia.
    pose proof (T1 nd_ctx_call Σ used fc fc' mm m' _ _ CTXm FRM' RA PR ltac:(right; lia)) as CTX'.
    destruct RA as (ART' & MI' & WM' & ST').
    clear XA ST MI ZRT. nd_after_call mm m' PR WM'.
    assert (INV' : nd_inv X spq f m' (repeat (Z_to_bv 8 0) 63) (Z_to_bv 64 (8 * k)) m' n tlen) by nd_inv_at m'.
    apply (aevt_evt RT AF PMc MST). num_ret_pc.
    eapply evt_eq; [| eapply (EVA nd_2f0 F' fc' m' (QΣ Σ) (nd_kmsx Σ used F' fc' m' CTX') k n tlen); [exact INV' | lia | lia | lia]].
    num_st_eq.
  Qed.
End NDTOP.
