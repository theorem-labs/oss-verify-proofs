(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound StartupHSBoth.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow HandoffKit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_libiface HandoffImage HandoffCLX RT_state RT_rep D_client Atp_activewA Pj_defsA Pj_handoffA El_defsA Dmp_hdefsA Dmp_pj_ifaceA Dmp_handoffA Dmp_recordA.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Instance hl_fx : PropExec.FPState := PropExec.fx0.
#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GWf.

Lemma hs_libdmp_lib : forall (A : atable) (nx0 : nat) (LIMIT : Z) (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs),
  (forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None) ->
  APS.hull_ok A -> (forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a) ->
  forall (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model),
  APS.cs_ok bsegs A nx0 LIMIT SINV argH FS0 E ch R FULL model ->
  forall A' : list (Z * Z), (forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true) ->
  hs_libdmp_ok ch = true -> el_libA (mH FULL model A').
Proof.
  intros A nx0 LIMIT SINV argH FS0 H1 H2 H3 E ch R FULL model HC A' HA' HT.
  destruct (hs_libdmp_gen A nx0 LIMIT SINV argH FS0 H1 H2 H3 E ch R FULL model HC A' HA' HT) as [(L & B & W) (HE & HU & HTL)].
  split; [split; [exact L| split; [left; exact B| exact W]]|].
  split; [exact HE| split; [exists false; exact HU| exact HTL]].
Qed.

Lemma client_dmp_hs : forall h ch, HS_both h = Some ch -> hs_libdmp_ok ch = true.
Proof. intros h ch H. exact (HS_libdmp_ok h ch H). Qed.

Definition client_dmp (PJ : forall PMc, pj_root_cpsA RTA PMc) : client_B := mkClientB el_libA el_lib_loc hs_libdmp_ok hs_libdmp_lib (dmp_cl_fuzz PJ).
