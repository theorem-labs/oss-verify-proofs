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
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx I_lkit Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_abig Sj_num_acall Sj_num_acall2 Sj_num_aframe Sj_num_lm_pro Sj_num_lm_enter Sj_num_lm_leave
  Sj_num_lm_kit Sj_num_lm_defs Sj_num_lm_tkit Sj_num_lm_a Sj_num_lm_b Sj_num_lm_c1 Sj_num_lm_c2 Sj_num_lm_c3 Sj_num_lm_top.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_zc_hook | asan_zcp_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section LMTOP.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RTF : rt_contracts_f RT.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.
  Hypothesis NLA : num_lits_acc RT.

  Variables (Σ0 Σ1 : rts RT) (K : config -> Prop).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (X lo d spq f g : Z) (kg : nat) (me : mem).
  Notation SP := (bv_unsigned sp).
  Notation S := (f / 8 + 2147450880)%Z.
  Notation Y := 0x2b8e0%Z.
  Hypothesis ETP : tp = Z_to_bv 64 0x6a0068.
  Hypothesis ROOM : (lo + LMA_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis LOR : (rt_sp0 RT Σ0 - STACK_WIN <= lo)%Z.
  Hypothesis EF : rt_frames RT Σ1 = (f, 5%nat) :: rt_frames RT Σ0.
  Hypothesis EL : rt_live RT Σ1 = rt_live RT Σ0.
  Hypothesis ES : rt_sp0 RT Σ1 = rt_sp0 RT Σ0.
  Hypothesis EC : rt_credit RT Σ1 = (rt_credit RT Σ0 - 1)%Z.
  Hypothesis SPQ : ((d = 0 \/ d = 16) /\ spq = SP - 256 - d)%Z.
  Hypothesis NF : (f mod 64 = 0 /\ 0x6c2000 <= f /\ f + 2040 <= lo /\ (f + 2040 <= S \/ S + 255 <= f) /\ 0 <= S /\ S + 255 <= lo)%Z.
  Hypothesis X8 : (X mod 8 = 0)%Z.
  Hypothesis XG : In (g, kg) (rt_frames RT Σ0) /\ (g <= X)%Z /\ (X + 504 <= g + fs_size kg - 8)%Z.
  Hypothesis XNUM : (0x6c2000 <= X /\ X + 504 <= lo /\ (X + 504 <= X / 8 + 2147450880 \/ X / 8 + 2147450880 + 63 <= X)
                     /\ 0 <= X / 8 + 2147450880 /\ X / 8 + 2147450880 + 63 <= lo)%Z.
  Hypothesis SEP : ((X + 504 <= f \/ f + 2048 <= X) /\ (X + 504 <= S \/ S + 256 <= X)
                    /\ (X / 8 + 2147450880 + 63 <= f \/ f + 2048 <= X / 8 + 2147450880)
                    /\ (X / 8 + 2147450880 + 63 <= S \/ S + 256 <= X / 8 + 2147450880))%Z.

  Hypothesis HK : forall (Σ' : rts RT) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m', frm0 fc' ->
     rt_after RT Σ' SP lo me m' -> rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) SP [(X, X + 504)%Z] me m' ->
     abig RT Σ' m' X ->
     rt_frames RT Σ' = rt_frames RT Σ0 -> rt_live RT Σ' = rt_live RT Σ0 -> rt_sp0 RT Σ' = rt_sp0 RT Σ0 ->
     (rt_credit RT Σ0 - 1 <= rt_credit RT Σ')%Z ->
     aevt RT PMc Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F' (ret_pc ra) fc' None m' (seg_rom asegs)).
  Collection TOPH := AF RTF FDO MST NLA ETP ROOM TOP SP16 LOR EF EL ES EC SPQ NF X8 XG XNUM SEP HK.

  Notation Q := (fun ms' => aevt RT PMc Σ1 K ms').
  Notation MREL := (lm_mrel RT Σ0 sp X me).
  Notation PARK := (lm_park ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo d spq f).

  Notation T1 L := (L RT AF RTF PMc FDO MST NLA Σ0 Σ1 K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X lo d spq f g kg me
                      ETP ROOM TOP SP16 LOR EF EL ES EC SPQ NF X8 XG XNUM SEP HK) (only parsing).
  Notation lm_ctx := (Sj_num_lm_top.lm_ctx RT Σ0 Σ1 ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 X lo d spq f me).
  Notation EVA L F fc ybs YL mb := (L sp gp tp F fc X lo d spq f Y ybs mb (T1 top_spq) ROOM TOP (proj1 NF) (conj (proj1 (proj2 NF)) (proj1 (proj2 (proj2 NF))))
                               (proj1 (proj2 (proj2 (proj2 NF)))) (proj2 (proj2 (proj2 (proj2 NF)))) X8
                               (conj (proj1 XNUM) (proj1 (proj2 XNUM))) (proj1 (proj2 (proj2 XNUM))) (proj2 (proj2 (proj2 XNUM))) SEP (T1 top_yr) YL) (only parsing).
  Notation LMS F fc pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 S) xs4 xs5 xs6 xs7 xs8 xs9
             (Z_to_bv 64 2147450880) xs11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Ltac top_env :=
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof NF as (N1 & N2 & N3 & N4 & N5 & N6); pose proof XNUM as (Q1 & Q2 & Q3 & Q4 & Q5); pose proof SEP as (E1 & E2 & E3 & E4);
    pose proof (T1 top_spq) as [Hd Hs]; pose proof ROOM as ROOM'; pose proof TOP as TOP'; unfold LMA_STACK, RT_STACK, USTACK_TOP in ROOM', TOP';
    pose proof (T1 top_inF) as HinF; pose proof (T1 top_f8) as F8; pose proof (eq_refl : fs_size 5 = 2048%Z) as FS5;
    pose proof (proj1 XG) as HinG0; pose proof (proj1 (proj2 XG)) as G1; pose proof (proj2 (proj2 XG)) as G2;
    assert (HinG : In (g, kg) (rt_frames RT Σ1)) by (rewrite EF; right; exact HinG0);
    pose proof (repeat_length (Z_to_bv 8 0) 63) as RL.

  Definition lm_loop_stmt (fuel : nat) : Prop :=
    forall (idx xlen zlen : Z) F fc (mb : mem) ybs xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xt3 ziw zsh,
      lm_ctx fc mb -> length ybs = 40%nat -> lm_inv X spq f Y ybs mb ziw zsh mb xlen zlen -> (1 <= idx < 5)%Z -> (5 - idx <= Z.of_nat fuel)%Z ->
      aevt RT PMc Σ1 K (LMS F fc 0xe227c (Z_to_bv 64 xlen) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (X + 8 * idx)) (Z_to_bv 64 Y) (Z_to_bv 64 (1 - idx))
                            (Z_to_bv 64 (X + 8 * idx)) (Z_to_bv 64 idx) (Z_to_bv 64 5) (Z_to_bv 64 (-8)) xt3 (Z_to_bv 64 X) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 608)) mb).

  Lemma lm_khead : forall fuel, lm_loop_stmt fuel -> forall F fc mb ybs, lm_ctx fc mb -> length ybs = 40%nat -> lm_head_k sp gp tp F fc X spq f Y ybs mb Q (5 - Z.of_nat fuel).
  Proof using TOPH.
    intros fuel HL F fc mb ybs CTX YL. unfold lm_head_k. intros until mm. intros INV Hidx.
    pose proof INV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MU & WM). unfold lm_WL in MU.
    apply evt_done.
    eapply (HL idx xlen zlen F fc mm ybs); [exact (T1 top_ctx_step fc mb mm CTX MU WM) | exact YL | exact (T1 lm_inv_rebase ybs mb ziw zsh mm xlen zlen INV) | lia | lia].
  Qed.

  Lemma lm_kmset : forall fuel, lm_loop_stmt fuel -> forall F fc mb ybs, lm_ctx fc mb -> length ybs = 40%nat -> lm_mset_k sp gp tp F fc X spq f Y ybs mb Q (5 - Z.of_nat fuel).
  Proof using TOPH.
    intros fuel HL F fc mb ybs CTX YL. unfold lm_mset_k. intros until mm. intros INV Hidx Hk Hxl.
    pose proof INV as ((w16 & j128 & j136 & SPILL) & (xbs & XA & XL) & XN & LEN & ZLN & ZR & (zibs & ZIA & ZIL) & ZIC & ZSH & YB & MI & MU & WM).
    unfold lm_WL in MU. unfold lm_spill in SPILL.
    pose proof (T1 top_ctx_step fc mb mm CTX MU WM) as CTXm. pose proof CTXm as (FRM & ARTm & MRm & PKm).
    pose proof PKm as (_ & _ & _ & _ & _ & _ & ST).
    top_env. clear CTX MU WM INV.
    apply evt_done.
    assert (XFRm : exists f0 c, In (f0, c) (rt_frames RT Σ1) /\ (f0 <= X)%Z /\ (X + Z.of_nat (length xbs) <= f0 + fs_size c - 8)%Z)
      by (exists g, kg; split; [exact HinG| rewrite XL; lia]).
    eapply (aevt_memset_u8 RT AF RTF PMc FDO MST Σ1 K mm X xbs 63 lo (Z_to_bv 64 spq) XA X8 ltac:(lia) ltac:(rewrite XL; lia) ltac:(rewrite XL; lia)
              ltac:(rewrite XL; lia) ZR XFRm ARTm MI (T1 top_cok mm ST)) with (dz := (8 * xlen)%Z) (nz := (8 * (idx + k - xlen))%Z) (cb := Z_to_bv 8 0);
      [reflexivity | reflexivity | reflexivity | lia | lia | rewrite XL; lia | lia | exact FRM | ].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' xbs' FRM' RA PR XA' XL'.
    rewrite ?unsigned_lit in RA, PR by lia.
    pose proof (T1 lm_ctx_call fc fc' mm m' _ _ CTXm FRM' RA PR ltac:(right; lia)) as CTX'.
    destruct RA as (ART' & MI' & WM' & ST').
    pose proof (agree_of_pres_ex _ _ _ _ _ mm m' (fun x => aclient (rt_live RT Σ1) (rt_frames RT Σ1) spq x /\ ~ (X + 8 * xlen <= x < X + 8 * xlen + 8 * (idx + k - xlen))%Z) PR (fun x H => H)) as AG.
    clear XA ST MI YB.
    destruct (image_readable_b asegs m' 40 Y ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (ybs' & YL' & YB').
    rt_transport_with mm m' AG WM' ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?repeat_length, ?ZIL in Hx; cbv beta; split; [aclient_tac| lia]).
    pose proof (munch_refl (lm_WL X spq f) m') as MU1. pose proof (wmono_refl asegs m') as WM1.
    assert (INV' : lm_inv X spq f Y ybs' m' ziw (repeat (Z_to_bv 8 0) 63) m' xlen zlen).
    { unfold lm_inv, lm_spill. split; [exists w16, j128, j136; exact SPILL|]. split; [exists xbs'; split; [exact XA'| lia]|].
      split; [exact XN|]. split; [lia|]. split; [lia|]. split; [exact ZR|]. split; [exists zibs; split; [exact ZIA| exact ZIL]|].
      split; [exact ZIC|]. split; [exact ZSH|]. split; [exact YB'|]. split; [exact MI'|]. split; [exact MU1| exact WM1]. }
    apply (aevt_evt RT AF PMc MST). num_ret_pc.
    eapply evt_eq; [| eapply (EVA lm_2a4 F' fc' ybs' YL' m' (T1 top_shpy m' (proj1 (proj2 CTX'))) Q (5 - Z.of_nat fuel)%Z (lm_khead fuel HL F' fc' m' ybs' CTX' YL') (T1 lm_kexit F' fc' m' CTX')
                              idx k (idx + k)%Z xlen zlen); [exact INV' | exact Hidx | lia | reflexivity | lia]].
    num_st_eq.
  Qed.

End LMTOP.
