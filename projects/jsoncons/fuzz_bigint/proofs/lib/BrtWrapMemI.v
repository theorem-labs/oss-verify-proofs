(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct RefMemcpyLib MemSplit MemsetLib HeapIface HeapIfaceA IcptIfaceAB0 ArtMem ArtRuns ArtBridge BrtInv BrtFsInv BrtFsInvLaws BrtInvFrame BrtIfaceFrame Bo0RegionPoisoned.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import BrtWrapMemset BrtWrapCopy BrtWrapCopyI.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section WMI.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Variable L : asan_layout.
Variable IL : icpt_layout.
Hypothesis HLsegs : hl_segs L = ASEGS.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x634000.
Hypothesis HLmemset : hl_asan_memset L = 0x5e7f0.
Hypothesis HLmemcpy : hl_asan_memcpy L = 0x5e354.
Hypothesis HLmemmove : hl_asan_memmove L = 0x5ea30.
Hypothesis HLscrmem : hl_scr_mem L = 2560.
Hypothesis HILmemcpy : icl_memcpy IL = 0x5e350.
Hypothesis HILmemmove : icl_memmove IL = 0x5e34c.
Hypothesis HLroimg : forall a, hl_rt_ro L a -> 0x10000 <= a < 0x634000.
Hypothesis HLstimg : forall a, hl_rt_static L a -> 0x10000 <= a < 0x634000.
Hypothesis HLst : forall a, art_zone_statics a -> hl_rt_static L a.
Hypothesis HLtls : forall a, (rn_tp rn - 88 <= a < rn_tp rn - 80 \/ rn_tsd rn + 8 * rn_key rn <= a < rn_tsd rn + 8 * rn_key rn + 8
                              \/ 0x611900 <= a < 0x611908 \/ 0x611930 <= a < 0x611938 \/ rn_tp rn <= a < rn_tp rn + 8
                              \/ rn_tp rn + rn_loff rn <= a < rn_tp rn + rn_loff rn + 4) -> hl_rt_static L a.
Hypothesis HLro : forall a, 0x10000 <= a < 0xd8000 -> hl_rt_ro L a.
Hypothesis HLcs : forall a, (0xd82a0 <= a < 0xd82a8 \/ 0xd8328 <= a < 0xd8338 \/ rn_tp rn + 8 <= a < rn_tp rn + 16) -> hl_rt_static L a.   (* [comment removed for export] *)
#[local] Abbreviation HI := (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).

Let AFL : art_alloc_rep_frame_law art_fsg MAPS0 RESV0 := art_alloc_rep_frame_law_proved art_fsg MAPS0 RESV0.
Let HLlsan : forall a, rn_tp rn + rn_loff rn <= a < rn_tp rn + rn_loff rn + 4 -> hl_rt_static L a.
Proof. intros a Ha. apply HLtls. do 5 right. exact Ha. Qed.
Let PRIVZ : forall (G : art_gs art_fsg) LB FF LK A (M Mr : word -> option byte) (lazy : list (word * word)),
  art_alloc_rep art_fsg rn G LB Mr -> art_fsinv rn (g_fs art_fsg G) FF LK M -> art_client_ok rn LB FF LK A M ->
  live_ok MAPS0 RESV0 (rn_HI rn) (art_live (g_log art_fsg G)) -> art_kn_ok MAPS0 RESV0 rn -> art_lazy_ok art_fsg rn G A lazy -> art_eager_ok LB A lazy ->
  forall a, art_alloc_zone art_fsg rn G a -> ~ in_block LB a -> art_private L (rn_ar rn) LB FF a.
Proof. intros G LB FF LK A M Mr lazy REP FS CLI LV KN _ _. exact (art_priv_zone MAPS0 RESV0 rn L HLlo HLhi HLst HLtls HLro G LB FF LK A M Mr REP FS CLI LV KN). Qed.
Let PRIVF : forall (G : art_gs art_fsg) LB FF LK A (M Mr : word -> option byte) (lazy : list (word * word)),
  art_alloc_rep art_fsg rn G LB Mr -> art_fsinv rn (g_fs art_fsg G) FF LK M -> art_client_ok rn LB FF LK A M ->
  live_ok MAPS0 RESV0 (rn_HI rn) (art_live (g_log art_fsg G)) -> art_kn_ok MAPS0 RESV0 rn -> art_lazy_ok art_fsg rn G A lazy -> art_eager_ok LB A lazy ->
  forall a, fs_zone3 rn a -> ~ in_fframe FF a -> art_private L (rn_ar rn) LB FF a.
Proof. intros G LB FF LK A M Mr lazy REP FS CLI LV KN _ _. exact (art_priv_fs3 MAPS0 RESV0 rn L HLlo HLhi HLtls G LB FF LK A M Mr REP FS CLI LV KN). Qed.
Let PRIVCS : forall (G : art_gs art_fsg) LB FF LK A (M Mr : word -> option byte) (lazy : list (word * word)),
  art_alloc_rep art_fsg rn G LB Mr -> art_fsinv rn (g_fs art_fsg G) FF LK M -> art_client_ok rn LB FF LK A M ->
  live_ok MAPS0 RESV0 (rn_HI rn) (art_live (g_log art_fsg G)) -> art_kn_ok MAPS0 RESV0 rn -> art_lazy_ok art_fsg rn G A lazy -> art_eager_ok LB A lazy ->
  forall a, cs_zone rn a -> art_private L (rn_ar rn) LB FF a.
Proof. intros G LB FF LK A M Mr lazy REP FS CLI LV KN _ _. exact (art_priv_cs MAPS0 RESV0 rn L HLlo HLhi HLcs G LB FF LK A M Mr REP FS CLI LV KN). Qed.

Lemma lit_5e660 : Z_to_bv 64 0x5e7f0 = (0x5e7f0%bv : word). Proof. apply bv_eq. reflexivity. Qed.

Theorem art_amemset : amemset_spec L (rn_ar rn) scfg HI.
Proof.
  intros fx R M model LB FF LK cr A dst c n K PRE H11 POST.
  destruct PRE as (INV & Hh & HMI & H10 & H12 & Hn & H4 & Hret & AST & AACC & CLW & DOK & KT0 & APPR).
  unfold amem_post in POST. rewrite HLsegs, HLscrmem in *. rewrite HLmemset, lit_5e660.
  apply (art_wrap_memset MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx AFL L HLsegs HLlo HLhi HLroimg HLstimg HLlsan PRIVZ PRIVF PRIVCS
           R M model LB FF LK cr A dst c n K INV Hh HMI H10 H12 Hn Hret AST AACC CLW DOK KT0 APPR H11).
  intros R' M' model' Q10 RP BY FR SD RT MI' RI'. apply (POST R' M' model' Q10 RP); try assumption.
Qed.

Section Copy.
Variables (pc : Z) (pcw : word) (FRB : Z).
Hypothesis Epc : Z_to_bv 64 pc = pcw.
Hypothesis FRB_rng : 2048 <= FRB <= 2560.
Hypothesis RUNX : forall fx : PropExec.FPState, @copy_run_spec fx pcw FRB.
Lemma art_amemcpy_at : amemcpy_spec_at L (rn_ar rn) scfg HI pc false.
Proof.
  intros fx R M model LB FF LK cr A dst src n bs K PRE H11 AACCS SR APPS CLSS RDS NOV POST.
  destruct PRE as (INV & Hh & HMI & H10 & H12 & Hn & H4 & Hret & AST & AACC & CLW & DOK & KT0 & APPR).
  unfold amem_post in POST. rewrite HLsegs, HLscrmem in *. rewrite Epc.
  apply (art_wrap_copy MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx AFL L HLsegs HLlo HLhi HLroimg HLstimg HLlsan PRIVZ PRIVF PRIVCS pcw FRB FRB_rng (RUNX fx)
           R M model LB FF LK cr A dst src n bs K INV Hh HMI H10 H12 Hn Hret AST AACC CLW DOK KT0 APPR H11 AACCS SR APPS CLSS RDS (NOV eq_refl)).
  intros R' M' model' Q10 RP BY FR SD RT MI' RI'. apply (POST R' M' model' Q10 RP); try assumption.
Qed.
End Copy.

Theorem art_amemcpy : amemcpy_spec L (rn_ar rn) scfg HI.
Proof. unfold amemcpy_spec. rewrite HLmemcpy. apply (art_amemcpy_at 0x5e354 (0x5e354 : word) 2216 ltac:(apply bv_eq; reflexivity) ltac:(lia) (fun fx => @copy_run_asan_memcpy fx)). Qed.
Theorem art_amemmove : amemmove_spec L (rn_ar rn) scfg HI.
Proof. unfold amemmove_spec. rewrite HLmemmove. apply (art_amemcpy_at 0x5ea30 (0x5ea30 : word) 2216 ltac:(apply bv_eq; reflexivity) ltac:(lia) (fun fx => @copy_run_asan_memmove fx)). Qed.
Theorem art_amemcpy_libc : amemcpy_libc_spec L (rn_ar rn) IL scfg HI.
Proof. unfold amemcpy_libc_spec. rewrite HILmemcpy. apply (art_amemcpy_at 0x5e350 (0x5e350 : word) 2232 ltac:(apply bv_eq; reflexivity) ltac:(lia) (fun fx => @copy_run_memcpy_libc fx)). Qed.
Theorem art_amemmove_libc : amemmove_libc_spec L (rn_ar rn) IL scfg HI.
Proof. unfold amemmove_libc_spec. rewrite HILmemmove. apply (art_amemcpy_at 0x5e34c (0x5e34c : word) 2216 ltac:(apply bv_eq; reflexivity) ltac:(lia) (fun fx => @copy_run_memmove_libc fx)). Qed.
End WMI.
