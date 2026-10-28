(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep Frame.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer SjPjCont.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 RT_iface4 D_defs D_kit D_clx D_libiface I_lkit
     Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit5A Atp_fzwA Pj_rtkA Pj_defsA Pj_cpsA Pj_copyA Pj_ser_defsA Pj_ser_kitA Pj_ser_callsA Pj_ser_trefA Pj_ser_ckitA
     Pj_ser_objkA Pj_ser_skitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).
Local Ltac dlia := Z.div_mod_to_equations; lia.

Section OKit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Section Mu.
  Variables (E : pjenvA) (D : nat) (C : conI).
  Hypothesis OK : pjenvA_ok E.
  Hypothesis CX : cctxA E D C.

  Lemma sbuf_read_muC : forall Σc st mr m o, CREFA RT E C Σc st mr -> munch (conWA E C st) mr m -> wmono bsegs mr m ->
    0 <= o < pa_sn E -> ov_read_bytes bsegs m (wa (pa_SBUF E + o)) 1 = Some [Z_to_bv 8 (pa_S E o)].
  Proof using AF OK CX.
    intros Σc st mr m o HR MU WM Ho.
    pose proof (CREFA_munch RT AF E D C Σc st mr m (sa_size st) OK CX HR MU WM) as (_ & _ & _ & _ & (_ & _ & _ & SB) & _). apply sbuf_read1; assumption.
  Qed.
  Lemma acc_sbuf_muC : forall Σc st mr m, CREFA RT E C Σc st mr -> munch (conWA E C st) mr m -> wmono bsegs mr m -> acc bsegs m (pa_SBUF E) (pa_NS E).
  Proof using AF OK CX.
    intros Σc st mr m HR MU WM.
    pose proof (CREFA_munch RT AF E D C Σc st mr m (sa_size st) OK CX HR MU WM) as (ART1 & _). pose proof HR as (_ & LV & _).
    pose proof (ok_sbuf E OK) as (_ & _ & _ & _ & INS).
    assert (INS' : In (pa_SBUF E, pa_NS E) (rt_live RT Σc)) by (rewrite LV; apply in_or_app; right; exact INS).
    exact (proj2 (af_acc_live RT AF Σc m _ _ ART1 INS')).
  Qed.
  Lemma shz_sbuf_muC : forall Σc st mr m, CREFA RT E C Σc st mr -> munch (conWA E C st) mr m -> wmono bsegs mr m -> shz m (pa_SBUF E) (pa_sn E).
  Proof using AF OK CX.
    intros Σc st mr m HR MU WM.
    pose proof (CREFA_munch RT AF E D C Σc st mr m (sa_size st) OK CX HR MU WM) as (ART1 & _). pose proof HR as (_ & LV & _).
    pose proof (ok_sbuf E OK) as (S16 & SN & _ & _ & INS). pose proof (ok_ns8 E OK) as N8.
    assert (INS' : In (pa_SBUF E, pa_NS E) (rt_live RT Σc)) by (rewrite LV; apply in_or_app; right; exact INS).
    pose proof (shz_live RT AF Σc m _ _ ART1 INS' ltac:(clear - S16; dlia)) as SH.
    eapply shz_sub; [exact SH| lia|]. clear - SN N8. dlia.
  Qed.

  Lemma shz_tabs_muC : forall Σc st mr m, CREFA RT E C Σc st mr -> munch (conWA E C st) mr m -> wmono bsegs mr m -> shz m PJ_TABS_A PJ_TABS_LEN.
  Proof using AF OK CX.
    intros Σc st mr m HR MU WM.
    pose proof (CREFA_munch RT AF E D C Σc st mr m (sa_size st) OK CX HR MU WM) as (ART1 & _).
    apply shz_tabs. exact (tabs_accA RT AF Σc m ART1).
  Qed.

  Lemma obuf_factsA : forall f Σc st m, octxA E C f -> CREFA RT E C Σc st m ->
    sa_buf st + sa_cap st <= pa_lo E /\ 0 < sa_buf st
    /\ (forall n, 0 <= n <= sa_cap st -> rng_class RT Σc (sa_buf st) n)
    /\ (forall y, sa_buf st <= y < sa_buf st + sa_cap st -> aclient (rt_live RT Σc) (rt_frames RT Σc) (ci_b C) y)
    /\ (forall y, sa_buf st <= y < sa_buf st + sa_cap st ->
          ~ (f <= y < f + 120) /\ ~ (f / 8 + 2147450880 <= y < f / 8 + 2147450880 + 16) /\ ~ (pa_SB E + 64 <= y < pa_SB E + 88)
          /\ ~ (shad (pa_SB E) <= y < shad (pa_SB E) + 11)).
  Proof using AF OK CX.
    intros f Σc st m OX HR. pose proof (buf_factsC RT AF E D C OK CX Σc st m HR) as (BL & B0 & RCB & CLB & APB). pose proof (oc_R E C f OX) as ER.
    split; [exact BL|]. split; [exact B0|]. split; [exact RCB|]. split; [exact CLB|].
    intros y Hy. destruct (APB y Hy) as (N1 & N2 & N3). split; [| split; [| split; [exact N2| exact N3]]].
    - intros C1. apply N1. exists f, (f + 120). split; [unfold cr_R; rewrite ER; right; left; reflexivity| exact C1].
    - intros C1. apply N1. exists (f / 8 + 2147450880), (f / 8 + 2147450896). split; [unfold cr_R; rewrite ER; right; right; left; reflexivity| clear - C1; lia].
  Qed.
End Mu.
End OKit.

Lemma cells_bytes_map_C1k : forall l : list byte, cells_bytes (map C1 l) = l.
Proof. induction l as [|b l IH]; [reflexivity|]. cbn [map cells_bytes cbytes app]. rewrite IH. reflexivity. Qed.
Lemma u8arr_of_sh16 : forall (m : mem) A l, rw_cells bsegs m A (sh16 l) -> u8arr bsegs m A l.
Proof.
  intros m A l H. unfold sh16 in H. split.
  - pose proof (rw_cells_bytes_at bsegs m A _ H) as B. rewrite cells_bytes_map_C1k in B. exact B.
  - eapply rw_cells_wr_at; [exact H|]. pose proof (sh16_size l) as SZ. unfold sh16 in SZ. rewrite SZ. lia.
Qed.
Lemma f1tmp_accB : forall (m : mem) (f : Z) (k : Z) (g : nat) (shp : list byte),
  rw_cells bsegs m (f / 8 + 2147450880) (sh16 shp) -> nth_error shp g = Some z8 -> 8 * (f / 8) = f -> 0 <= f -> k = 8 * Z.of_nat g -> acc bsegs m (f + k) 8.
Proof.
  intros m f k g shp SH HG Ef F0 Hk. apply (f3tmp_accA m f k g shp (u8arr_of_sh16 m _ _ SH) HG Ef F0 Hk).
Qed.

Ltac ostr_envA OK CX OX :=
  obj_envA OK CX OX;
  lazymatch type of CX with cctxA ?E ?D ?C =>
  let H := fresh in let D8 := fresh in let B32 := fresh in
  pose proof (env_rangesA E OK) as H;
  destruct H as (T0 & TL & _ & S0 & SL & S16 & D8 & B32 & _);
  assert (ED : 8 * (pa_DOC E / 8) = pa_DOC E) by (clear - D8; Z.div_mod_to_equations; lia);
  assert (ESB : 8 * (pa_SB E / 8) = pa_SB E) by (clear - B32; Z.div_mod_to_equations; lia); clear D8 B32
  end.
