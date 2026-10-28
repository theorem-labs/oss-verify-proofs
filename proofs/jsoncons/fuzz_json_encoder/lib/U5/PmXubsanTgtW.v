(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* The ubsan target half: the ubsan image realizes the plain spec at target_alloc_limit (2^39 = nbr_limit) for every
   input whose payload satisfies PHI0U. The ubsan twin of the plain driver (Pm6DrvMainW_u5) realizes specG over the
   ubsan heap instance (HIU, L0U, credit (K0U, B0U)); its library call consumes PHI (LCU.lib_call_okU), so the
   success branch needs PHI for the payload, which phi_okU gives; specG_eq then turns specG into spec (as
   PmXasanBaseW.xsrc_half does). The library assembly (layout, statics, call contract, budget) is a Section
   hypothesis here. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import ShapeAlg SpinAlg SpinAlgX Spec BigintSpec SpecG HeapIface LibIface LibIfaceFp.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import RunEnv PropExec StoreOk MmapSim.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmXubsanStmt Pm6DrvLib_u5 Pm6DrvLibL_u5 Pm6DrvG_u5 Pm6DrvD_u5 Pm6DrvMainW_u5 Pm6HeapBridge_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Lib Require Import LibContractU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Heap Require Import HeapIfaceU HeapInstU HeapClosedU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Bridge Require Import PmHeapInst6_u5.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PmXubsanTgtW.
Import PmXubsanStmt.

Section FPX_1.
#[local] Existing Instance PropExec.fx0.

(* The driver budget (Pm6DrvMainW_u5's Hbudget) for any library layout whose credit is LCU.pm_creditxU, from
   LCU.creditU_fits_driver: Pm6DrvG.cred at k = 0 after the driver's 65536-byte buffer, over (K0U, B0U). *)
Lemma budget_of_lay : forall sptop Lay n, LCU.lay_creditU (L0U sptop) Lay -> 0 <= n < 67108864 ->
  cred (L0U sptop) (hl_k_per_malloc (L0U sptop) + 4 * fst (ll_credit Lay n))
       (n + hl_b_overhead (L0U sptop) + 4 * snd (ll_credit Lay n)) 0 (debit (L0U sptop) (K0U, B0U) 65536).
Proof.
  intros sptop Lay n HL Hn. rewrite (HL n).
  assert (HK : hl_k_per_malloc (L0U sptop) = 8) by (rewrite L0U_kpm; exact KPM_val).
  assert (HB : hl_b_overhead (L0U sptop) = 3609042) by (rewrite L0U_bov; exact BOV_val).
  destruct (LCU.creditU_fits_driver (L0U sptop) n HK HB ltac:(lia)) as [C1 C2].
  unfold cred, CAPk, debit. cbn [fst snd]. rewrite Z.pow_0_r. rewrite HK, HB. lia.
Qed.

Section Tgt.
  Variable LayF : word -> lib_layout.
  Variable LStF : word -> lib_statics.
  Hypothesis DLLF : forall sp, valid_sp sp -> drv_lib_layout (LayF sp) (L0U (bv_unsigned sp)).
  Hypothesis LIOKUF : forall sp, valid_sp sp -> LCU.lib_iface_okU (LayF sp) cfgU (HIU (bv_unsigned sp)) (LStF sp) PHI0U.
  Hypothesis LXokF : forall sp, valid_sp sp -> lib_exit_ok (LStF sp).
  Hypothesis LCREDF : forall sp, valid_sp sp -> LCU.lay_creditU (L0U (bv_unsigned sp)) (LayF sp).

  Lemma cfgU_alloc : sc_alloc cfgU = false.  Proof. reflexivity. Qed.
  Lemma cfgU_fs : sc_fs cfgU = true.  Proof. reflexivity. Qed.

  (* The driver over the ubsan heap realizes specG at target_alloc_limit (cf. Pm6HeapBridgeW.src0_realizes_specG_heap_lim). *)
  Lemma tgt_specG : src_realizes_stmtG_lim cfgU PHI0U target_alloc_limit.
  Proof.
    apply (src0_realizes_specG_lim cfgU (fun sp => L0U (bv_unsigned sp)) (fun sp => HIU (bv_unsigned sp)) LayF LStF (K0U, B0U)).
    - intros sp Hsp. exact (HIU_iface_ok_closed (bv_unsigned sp) cfgU cfgU_alloc).
    - exact drv_layout_L0U.
    - exact DLLF.
    - exact LIOKUF.
    - exact LXokF.
    - intros lim sp a0s path envp uid hw rdraw tid regs mem brk mbase Hlim Hsp Hbrk Hmb Hva Hve Htid ME.
      exact (main_hiu_heap0 sp a0s path envp uid hw rdraw tid regs mem Hva Hve Hsp Htid ME brk mbase lim Hlim Hbrk Hmb).
    - exact cfgU_fs.
    - intros sp n Hsp Hn. exact (budget_of_lay (bv_unsigned sp) (LayF sp) n (LCREDF sp Hsp) Hn).
    - rewrite target_alloc_limit_val. lia.
  Qed.

  Theorem pm_xubsan_tgt : pm_xubsan_tgt_stmt cfgU PHI0U.
  Proof.
    intros sp brk mbase rdraw inp Hsp Hbrk Hmb Hfits Hva Hve Hvfs Hcreds Hhw Hva48 HPHIOK.
    apply (srz_conseq _ _ _ (specG (fun d => PHI0U (payload d)) (in_argv inp) (in_fs inp))).
    - exact (tgt_specG sp brk mbase rdraw inp Hsp Hbrk Hmb Hfits Hva Hve Hvfs Hcreds HPHIOK).
    - apply specG_eq. intros a0 path data Hargv Hlen Hne Hnd Hlk Hhdr.
      exact (HPHIOK a0 path Hargv Hlen Hne Hnd data Hlk Hhdr).
  Qed.
End Tgt.
End FPX_1.
End PmXubsanTgtW.
