(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound StartupHSAsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow HandoffKit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_libiface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import HandoffImage HandoffCLX RT_state RT_rep RT_refillstmt D_client Pj_defsA Pj_handoffA El_defsA El_frontA El_recordA El_handoffA.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Instance hl_fx : PropExec.FPState := PropExec.fx0.
#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GWf.

Lemma el_lib_rng_fp : forall x, el_lib_rng x -> in_ranges LIB_FP x.
Proof.
  intros x [H|[H|H]].
  - destruct H as (lo & hi & Hin & R). unfold EL_LIB_FP in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [exists lo, hi; split; [exact Hin| exact R]|].
    cbn [In] in Hin. unfold EL_UNW_A, EL_EHG_A, EL_TPLOC_A, TPV_A in Hin.
    destruct Hin as [Hin|[Hin|[Hin|[]]]]; inversion Hin; subst lo hi.
    + exists 0x6a7d90, 0x6a7d98. split; [unfold LIB_FP; cbn; tauto| lia].
    + exists 0x6a6478, 0x6a6484. split; [unfold LIB_FP; cbn; tauto| lia].
    + exists 0x6a7e38, 0x6a7e40. split; [unfold LIB_FP; cbn; tauto| lia].
  - exists 0x6a6478, 0x6a6484. split; [unfold LIB_FP; cbn; tauto| unfold EL_EHG_A in H; lia].
  - exists 0x6a7e38, 0x6a7e40. split; [unfold LIB_FP; cbn; tauto| unfold EL_TPLOC_A, TPV_A in H; lia].
Qed.

Lemma el_lib_loc : fp_local LIB_FP el_libA.
Proof. intros m m' H AG. apply (el_libA_agree m m' H). intros a Ha. apply AG. exact (el_lib_rng_fp _ Ha). Qed.

Lemma hs_libel_lib : forall (A : atable) (nx0 : nat) (LIMIT : Z) (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs),
  (forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment asegs (bv_unsigned a) 1 = None) ->
  APS.hull_ok A -> (forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a) ->
  forall (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model),
  APS.cs_ok asegs A nx0 LIMIT SINV argH FS0 E ch R FULL model ->
  forall A' : list (Z * Z), (forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true) ->
  hs_libel_ok ch = true -> el_libA (mH FULL model A').
Proof.
  intros A nx0 LIMIT SINV argH FS0 H1 H2 H3 E ch R FULL model HC A' HA' HT.
  destruct (hs_libel_gen A nx0 LIMIT SINV argH FS0 H1 H2 H3 E ch R FULL model HC A' HA' HT) as [(L & B & W) (HE & HU & HTL)].
  split; [split; [exact L| split; [left; exact B| exact W]]|].
  split; [exact HE| split; [exists false; exact HU| exact HTL]].
Qed.

Lemma client_el_hs : forall h ch, HS_asan h = Some ch -> hs_libel_ok ch = true.
Proof. intros h ch H. exact (HS_libel_ok h ch H). Qed.

Section CL.
Hypothesis RF : refill_stmt.
Hypothesis DUMP : forall PMc, dump_cpsA RTA PMc.
Definition client_el : client_B := mkClientB el_libA el_lib_loc hs_libel_ok hs_libel_lib (fun RC2 => el_cl_fuzz RF DUMP RC2).
End CL.
