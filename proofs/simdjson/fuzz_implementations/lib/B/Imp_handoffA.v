(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound StartupHSBoth.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow HandoffKit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_libiface HandoffImage HandoffCLX RT_state RT_rep Atp_activewA Atp_handoffA Pj_defsA Imp_hdefsA Imp_ios_defsA Imp_libifaceA.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Instance hl_fx : PropExec.FPState := PropExec.fx0.
#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GWf.

Definition locb_cellsAH (ch : acs) : list cell :=
  locb_cellsA (hs_blob ch 0x6bcc28 64) (hs_blob ch 0x6bcc74 380) (hs_blob ch 0x6bcdfa 22) (hs_blob ch 0x6bce19 199) (hs_blob ch 0x6bceec 4)
              (hs_blob ch 0x6bcefc 180) (hs_blob ch 0x6bcfb8 400) (hs_blob ch 0x6bd150 120) (hs_blob ch 0x6bd1d0 8) (hs_blob ch 0x6bd1da 6)
              (hs_blob ch 0x6bd1f8 64) (hs_blob ch 0x6bd248 24) (hs_blob ch 0x6bd268 56) (hs_blob ch 0x6bd2a8 24) (hs_blob ch 0x6bd2c8 2064).

Definition hs_imp_ok (ch : acs) : bool :=
  (hs_lib_ok ch
   && hs_rw_cells ch IMP_AVL_GUARD_A g00 && hs_rw_cells ch IMP_AVP_SPAN_A [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] && hs_rw_cells ch IMP_AVP_GUARD_A g00
   && hs_rw_cells ch IMP_AVP_ARR_A [C8 (Z_to_bv 64 0)]
   && hs_rw_cells ch IMP_VEC_OBJ_A [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] && hs_rw_cells ch IMP_GUARD_A g00
   && hs_rw_cells ch PJ_LOC_LO_A (locb_cellsAH ch)
   && hs_rw_cells ch LOC_CVC [C8 (Z_to_bv 64 VT_CVC)] && hs_rw_cells ch LOC_CVW [C8 (Z_to_bv 64 VT_CVW)] && hs_rw_cells ch (LOC_CVW + 16) [C8 (Z_to_bv 64 CLOC)]
   && hs_rw_cells ch (TPV_A - 48) [C8 (Z_to_bv 64 (LIBC_A + 56))]
   && hs_rw_cells ch PJ_LOCKW_A [C4 (Z_to_bv 64 0)])%bool.

Section Lib.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.

Theorem hs_imp_gen : forall A' : list (Z * Z),
  (forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true) ->
  hs_imp_ok ch = true -> imp_libA None (mH FULL model A').
Proof using SEGS_in_hull HULL_ok argH_high HC.
  intros A' HA' HT. unfold hs_imp_ok in HT.
  apply andb_prop in HT as [HT K13]. apply andb_prop in HT as [HT K12]. apply andb_prop in HT as [HT K11]. apply andb_prop in HT as [HT K10]. apply andb_prop in HT as [HT K9].
  apply andb_prop in HT as [HT K8]. apply andb_prop in HT as [HT K7]. apply andb_prop in HT as [HT K6]. apply andb_prop in HT as [HT K5]. apply andb_prop in HT as [HT K4].
  apply andb_prop in HT as [HT K3]. apply andb_prop in HT as [K1 K2].
  pose proof (fun a cs H => hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' a cs H) as RW.
  unfold hs_lib_ok in K1. apply andb_prop in K1 as [K1 L4]. apply andb_prop in K1 as [K1 L3]. apply andb_prop in K1 as [L1 L2].
  split; [| split; [| split; [| split]]].
  - split; [split; [exact (RW _ _ L1)| split; [exact (RW _ _ L2)| split; [exact (RW _ _ L3)| exact (RW _ _ L4)]]]|].
    split; [exact (RW _ _ K2)|]. split; [exact (RW _ _ K3)|]. split; [exact (RW _ _ K4)|]. split; [exact (RW _ _ K5)|]. split; [exact (RW _ _ K6)| exact (RW _ _ K7)].
  - do 15 eexists. exact (RW _ _ K8).
  - split; [exact (RW _ _ K9)| split; [exact (RW _ _ K10)| exact (RW _ _ K11)]].
  - exact (RW _ _ K12).
  - exact (RW _ _ K13).
Qed.
End Lib.

Lemma hs_imp_0 : hs_imp_ok HS_both_0 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_imp_1000 : hs_imp_ok HS_both_1000 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_imp_2000 : hs_imp_ok HS_both_2000 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_imp_3000 : hs_imp_ok HS_both_3000 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma HS_imp_ok : forall h ch, HS_both h = Some ch -> hs_imp_ok ch = true.
Proof.
  intros h ch. unfold HS_both.
  apply (hs_if_some_lib (fun c => hs_imp_ok c = true)); [exact hs_imp_3000|].
  apply (hs_if_some_lib (fun c => hs_imp_ok c = true)); [exact hs_imp_2000|].
  apply (hs_if_some_lib (fun c => hs_imp_ok c = true)); [exact hs_imp_1000|].
  apply (hs_if_some_lib (fun c => hs_imp_ok c = true)); [exact hs_imp_0| discriminate].
Qed.
