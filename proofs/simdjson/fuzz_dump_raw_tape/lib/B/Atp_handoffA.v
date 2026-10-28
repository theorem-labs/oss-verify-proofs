(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound
  StartupHSBoth.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import HandoffKit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs HandoffImage HandoffCLX RT_state RT_rep Atp_activewA.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Instance hl_fx : PropExec.FPState := PropExec.fx0.

#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GWf.
Definition hs_lib_ok (ch : acs) : bool :=
  (hs_rw_cells ch 0x6aa2c0 [C8 (Z_to_bv 64 0)] && hs_rw_cells ch 0x6aa2e0 [C1 z8; C1 z8]
   && hs_rw_cells ch 0x6aa360 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
   && hs_rw_cells ch 0x6aa3c0 [C1 z8; C1 z8])%bool.

Section Lib.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.

Theorem hs_lib_gen : forall A' : list (Z * Z),
  (forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true) ->
  hs_lib_ok ch = true -> sj_lib (mH FULL model A').
Proof using SEGS_in_hull HULL_ok argH_high HC.
  intros A' HA' HT. unfold hs_lib_ok in HT.
  apply andb_prop in HT as [HT H4]. apply andb_prop in HT as [HT H3]. apply andb_prop in HT as [H1 H2].
  left. unfold lib0.
  split; [exact (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ H1)|].
  split; [exact (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ H2)|].
  split; [exact (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ H3)|].
  exact (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ H4).
Qed.

End Lib.

Lemma hs_lib_0 : hs_lib_ok HS_both_0 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_lib_1000 : hs_lib_ok HS_both_1000 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_lib_2000 : hs_lib_ok HS_both_2000 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hs_lib_3000 : hs_lib_ok HS_both_3000 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma hs_if_some_lib : forall (P : acs -> Prop) (b : bool) (s : acs) (r : option acs) (ch : acs),
  P s -> (r = Some ch -> P ch) -> (if b then Some s else r) = Some ch -> P ch.
Proof. intros P b s r ch Ps Pr H. destruct b; [injection H as <-; exact Ps | exact (Pr H)]. Qed.

Lemma HS_lib_ok : forall h ch, HS_both h = Some ch -> hs_lib_ok ch = true.
Proof.
  intros h ch. unfold HS_both.
  apply (hs_if_some_lib (fun c => hs_lib_ok c = true)); [exact hs_lib_3000|].
  apply (hs_if_some_lib (fun c => hs_lib_ok c = true)); [exact hs_lib_2000|].
  apply (hs_if_some_lib (fun c => hs_lib_ok c = true)); [exact hs_lib_1000|].
  apply (hs_if_some_lib (fun c => hs_lib_ok c = true)); [exact hs_lib_0| discriminate].
Qed.
