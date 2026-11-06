(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct RefMemcpyLib MemSplit MemsetLib HeapIface HeapIfaceA HeapIfaceAEx HeapIfaceAEr IcptIfaceA ArtMem ArtRuns ArtBridge EarInv EarFsInv EarFsInvLaws EarInvFrame EarIfaceFrame Ea0RegionPoisoned.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import EarWrapMemset EarWrapCopy EarWrapCopyI.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
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
Hypothesis HLhi : hl_img_hi L = 0x698000.
Hypothesis HLmemset : hl_asan_memset L = 0x78ab4.
Hypothesis HLmemcpy : hl_asan_memcpy L = 0x78618.
Hypothesis HLmemmove : hl_asan_memmove L = 0x78cf4.
Hypothesis HLscrmem : hl_scr_mem L = 2560.
Hypothesis HILmemcpy : icl_memcpy IL = 0x78614.
Hypothesis HILmemmove : icl_memmove IL = 0x78610.
Hypothesis HLroimg : forall a, hl_rt_ro L a -> 0x10000 <= a < 0x698000.
Hypothesis HLstimg : forall a, hl_rt_static L a -> 0x10000 <= a < 0x698000.
Hypothesis HLst : forall a, art_zone_statics a -> hl_rt_static L a.
Hypothesis HLtls : forall a, (rn_tp rn - 88 <= a < rn_tp rn - 80 \/ rn_tsd rn + 8 * rn_key rn <= a < rn_tsd rn + 8 * rn_key rn + 8
                              \/ 0x675a78 <= a < 0x675a80 \/ 0x675aa8 <= a < 0x675ab0 \/ rn_tp rn <= a < rn_tp rn + 8
                              \/ rn_tp rn + rn_loff rn <= a < rn_tp rn + rn_loff rn + 4) -> hl_rt_static L a.
Hypothesis HLro : forall a, 0x10000 <= a < 0x13a000 -> hl_rt_ro L a.
Hypothesis HLcs : forall a, (0x13afd0 <= a < 0x13afd8 \/ 0x13b098 <= a < 0x13b0b0 \/ rn_tp rn + 8 <= a < rn_tp rn + 16) -> hl_rt_static L a.
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

#[using="Type"] Lemma lit_78a64 : Z_to_bv 64 0x78ab4 = (0x78ab4%bv : word). Proof. apply bv_eq. reflexivity. Qed.

#[using="Hwx HLsegs HLlo HLhi HLmemset HLscrmem HLroimg HLstimg HLst HLtls HLro HLcs AFL HLlsan PRIVZ PRIVF PRIVCS"] Theorem art_amemset : amemset_spec L (rn_ar rn) scfg HI.
Proof.
  intros fx R M model LB FF LK cr A dst c n K PRE H11 POST.
  destruct PRE as (INV & Hh & HMI & H10 & H12 & Hn & H4 & Hret & AST & AACC & CLW & DOK & KT0 & APPR).
  unfold amem_post in POST. rewrite HLsegs, HLscrmem in *. rewrite HLmemset, lit_78a64.
  apply (art_wrap_memset MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx AFL L HLsegs HLlo HLhi HLroimg HLstimg HLlsan PRIVZ PRIVF PRIVCS
           R M model LB FF LK cr A dst c n K INV Hh HMI H10 H12 ltac:(clear - Hn; change (2 ^ 27) with 134217728 in Hn; change (2 ^ 32) with 4294967296; lia) Hret AST AACC CLW DOK KT0 APPR H11).
  intros R' M' model' Q10 RP BY FR SD RT MI' RI'. apply (POST R' M' model' Q10 RP); try assumption.
Qed.

Section Copy.
Variables (pc : Z) (pcw : word) (FRB : Z).
Hypothesis Epc : Z_to_bv 64 pc = pcw.
Hypothesis FRB_rng : 2048 <= FRB <= 2560.
Hypothesis RUNX : forall fx : PropExec.FPState, @copy_run_spec fx pcw FRB.
#[using="Hwx HLsegs HLlo HLhi HLscrmem HLroimg HLstimg HLst HLtls HLro HLcs AFL HLlsan PRIVZ PRIVF PRIVCS pcw FRB Epc FRB_rng RUNX"] Lemma art_amemcpy_at : amemcpy_spec_at L (rn_ar rn) scfg HI pc false.
Proof.
  intros fx R M model LB FF LK cr A dst src n bs K PRE H11 AACCS SR APPS CLSS RDS NOV POST.
  destruct PRE as (INV & Hh & HMI & H10 & H12 & Hn & H4 & Hret & AST & AACC & CLW & DOK & KT0 & APPR).
  unfold amem_post in POST. rewrite HLsegs, HLscrmem in *. rewrite Epc.
  apply (art_wrap_copy MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx AFL L HLsegs HLlo HLhi HLroimg HLstimg HLlsan PRIVZ PRIVF PRIVCS pcw FRB FRB_rng (RUNX fx)
           R M model LB FF LK cr A dst src n bs K INV Hh HMI H10 H12 ltac:(clear - Hn; change (2 ^ 27) with 134217728 in Hn; change (2 ^ 32) with 4294967296; lia) Hret AST AACC CLW DOK KT0 APPR H11 AACCS SR APPS CLSS RDS (NOV eq_refl)).
  intros R' M' model' Q10 RP BY FR SD RT MI' RI'. apply (POST R' M' model' Q10 RP); try assumption.
Qed.
End Copy.

#[using="Hwx HLsegs HLlo HLhi HLmemcpy HLscrmem HLroimg HLstimg HLst HLtls HLro HLcs AFL HLlsan PRIVZ PRIVF PRIVCS"] Theorem art_amemcpy : amemcpy_spec L (rn_ar rn) scfg HI.
Proof. unfold amemcpy_spec. rewrite HLmemcpy. apply (art_amemcpy_at 0x78618 (0x78618 : word) 2216 ltac:(apply bv_eq; reflexivity) ltac:(lia) (fun fx => @copy_run_asan_memcpy fx)). Qed.
#[using="Hwx HLsegs HLlo HLhi HLmemmove HLscrmem HLroimg HLstimg HLst HLtls HLro HLcs AFL HLlsan PRIVZ PRIVF PRIVCS"] Theorem art_amemmove : amemmove_spec L (rn_ar rn) scfg HI.
Proof. unfold amemmove_spec. rewrite HLmemmove. apply (art_amemcpy_at 0x78cf4 (0x78cf4 : word) 2216 ltac:(apply bv_eq; reflexivity) ltac:(lia) (fun fx => @copy_run_asan_memmove fx)). Qed.
#[using="Hwx HLsegs HLlo HLhi HLscrmem HILmemcpy HLroimg HLstimg HLst HLtls HLro HLcs AFL HLlsan PRIVZ PRIVF PRIVCS"] Theorem art_amemcpy_libc : amemcpy_libc_spec L (rn_ar rn) IL scfg HI.
Proof. unfold amemcpy_libc_spec. rewrite HILmemcpy. apply (art_amemcpy_at 0x78614 (0x78614 : word) 2232 ltac:(apply bv_eq; reflexivity) ltac:(lia) (fun fx => @copy_run_memcpy_libc fx)). Qed.
#[using="Hwx HLsegs HLlo HLhi HLscrmem HILmemmove HLroimg HLstimg HLst HLtls HLro HLcs AFL HLlsan PRIVZ PRIVF PRIVCS"] Theorem art_amemmove_libc : amemmove_libc_spec L (rn_ar rn) IL scfg HI.
Proof. unfold amemmove_libc_spec. rewrite HILmemmove. apply (art_amemcpy_at 0x78610 (0x78610 : word) 2216 ltac:(apply bv_eq; reflexivity) ltac:(lia) (fun fx => @copy_run_memmove_libc fx)). Qed.

#[using="Hwx HLsegs HLlo HLhi HLmemset HLscrmem HLroimg HLstimg HLst HLtls HLro HLcs AFL HLlsan PRIVZ PRIVF PRIVCS"] Theorem art_amemsetN : HAR.amemsetN_spec L (rn_ar rn) scfg (fun _ : list (list Z) => HI).
Proof.
  intros D fx R M model LB FF LK cr A dst c n K PRE H11 POST.
  destruct PRE as (INV & Hh & HMI & H10 & H12 & Hn & H4 & Hret & AST & AACC & CLW & DOK & KT0 & APPR).
  unfold amem_post in POST. rewrite HLsegs, HLscrmem in *. rewrite HLmemset, lit_78a64.
  apply (art_wrap_memset MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx AFL L HLsegs HLlo HLhi HLroimg HLstimg HLlsan PRIVZ PRIVF PRIVCS
           R M model LB FF LK cr A dst c n K INV Hh HMI H10 H12 Hn Hret AST AACC CLW DOK KT0 APPR H11).
  intros R' M' model' Q10 RP BY FR SD RT MI' RI'. apply (POST R' M' model' Q10 RP); try assumption.
Qed.
Section CopyN.
Variables (pc : Z) (pcw : word) (FRB : Z).
Hypothesis Epc : Z_to_bv 64 pc = pcw.
Hypothesis FRB_rng : 2048 <= FRB <= 2560.
Hypothesis RUNX : forall fx : PropExec.FPState, @copy_run_spec fx pcw FRB.
#[using="Hwx HLsegs HLlo HLhi HLscrmem HLroimg HLstimg HLst HLtls HLro HLcs AFL HLlsan PRIVZ PRIVF PRIVCS pcw FRB Epc FRB_rng RUNX"] Lemma art_amemcpyN_at : HAR.amemcpyN_spec_at L (rn_ar rn) scfg (fun _ : list (list Z) => HI) pc.
Proof.
  intros D fx R M model LB FF LK cr A dst src n bs K PRE H11 AACCS SR APPS CLSS RDS NOV POST.
  destruct PRE as (INV & Hh & HMI & H10 & H12 & Hn & H4 & Hret & AST & AACC & CLW & DOK & KT0 & APPR).
  unfold amem_post in POST. rewrite HLsegs, HLscrmem in *. rewrite Epc.
  apply (art_wrap_copy MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx AFL L HLsegs HLlo HLhi HLroimg HLstimg HLlsan PRIVZ PRIVF PRIVCS pcw FRB FRB_rng (RUNX fx)
           R M model LB FF LK cr A dst src n bs K INV Hh HMI H10 H12 Hn Hret AST AACC CLW DOK KT0 APPR H11 AACCS SR APPS CLSS RDS NOV).
  intros R' M' model' Q10 RP BY FR SD RT MI' RI'. apply (POST R' M' model' Q10 RP); try assumption.
Qed.
End CopyN.
#[using="Hwx HLsegs HLlo HLhi HLmemcpy HLscrmem HLroimg HLstimg HLst HLtls HLro HLcs AFL HLlsan PRIVZ PRIVF PRIVCS"] Theorem art_amemcpyN : HAR.amemcpyN_spec_at L (rn_ar rn) scfg (fun _ : list (list Z) => HI) (hl_asan_memcpy L).
Proof. rewrite HLmemcpy. apply (art_amemcpyN_at 0x78618 (0x78618 : word) 2216 ltac:(apply bv_eq; reflexivity) ltac:(lia) (fun fx => @copy_run_asan_memcpy fx)). Qed.
#[using="Hwx HLsegs HLlo HLhi HLmemmove HLscrmem HLroimg HLstimg HLst HLtls HLro HLcs AFL HLlsan PRIVZ PRIVF PRIVCS"] Theorem art_amemmoveN : HAR.amemcpyN_spec_at L (rn_ar rn) scfg (fun _ : list (list Z) => HI) (hl_asan_memmove L).
Proof. rewrite HLmemmove. apply (art_amemcpyN_at 0x78cf4 (0x78cf4 : word) 2216 ltac:(apply bv_eq; reflexivity) ltac:(lia) (fun fx => @copy_run_asan_memmove fx)). Qed.
#[using="Hwx HLsegs HLlo HLhi HLscrmem HILmemcpy HLroimg HLstimg HLst HLtls HLro HLcs AFL HLlsan PRIVZ PRIVF PRIVCS"] Theorem art_amemcpy_libcN : HAR.amemcpyN_spec_at L (rn_ar rn) scfg (fun _ : list (list Z) => HI) (icl_memcpy IL).
Proof. rewrite HILmemcpy. apply (art_amemcpyN_at 0x78614 (0x78614 : word) 2232 ltac:(apply bv_eq; reflexivity) ltac:(lia) (fun fx => @copy_run_memcpy_libc fx)). Qed.
#[using="Hwx HLsegs HLlo HLhi HLscrmem HILmemmove HLroimg HLstimg HLst HLtls HLro HLcs AFL HLlsan PRIVZ PRIVF PRIVCS"] Theorem art_amemmove_libcN : HAR.amemcpyN_spec_at L (rn_ar rn) scfg (fun _ : list (list Z) => HI) (icl_memmove IL).
Proof. rewrite HILmemmove. apply (art_amemcpyN_at 0x78610 (0x78610 : word) 2216 ltac:(apply bv_eq; reflexivity) ltac:(lia) (fun fx => @copy_run_memmove_libc fx)). Qed.
End WMI.
