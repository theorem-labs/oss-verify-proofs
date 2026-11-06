(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import HttpRepA AWKit AWAuto AWAuto2 FakeKit HObjK HObjF H_pent_seg.
Import ListNotations.
Open Scope Z_scope.

Section W.
Context {HC : HasCeiling}.
Variable FI : fs_if.

Section PE2.
  Variables (q lo P : Z) (st : fsstate FI).
  Variables (gp tp : word) (F_ : bvmap 5 word) (fc : bv 32).
  Hypothesis POK : pe_okA FI q lo P st.

  #[using="lo POK"] Lemma dispXE : forall (q' : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 m (Q : machine_state -> Prop),
    pscr FI P st q' m -> mem_inv asegs m -> rw_cells asegs m (P + 452) [C4 (wz 0)] -> acc m (P + 452 + 4 - 1) ->
    (forall y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y28 y29 y30 y31,
       evt asegs Q (exitstA FI q st gp tp F_ fc q' 3 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y28 y29 y30 y31 m)) ->
    evt asegs Q (dispstA FI q P st gp tp F_ fc q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 m).
  Proof.
    intros q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 m Q (j0 & j256 & QC) MI EC HACC K.
    pose proof POK as POK'. destruct POK' as (CLO & LO & AL16 & QHI & PLO & PHI & PAL & PLB). clear PLB.
    unfold dispstA, pregs, eSH in *.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let a := reg_val 25 in
      destruct (AWAuto2.acc_loadw mm (P + 452) 4 a ltac:(lia) ltac:(clear - PAL; Z.div_mod_to_equations; lia) ltac:(lia) HACC ltac:(shadow_addr_tac)) as (k & SHR & Hk) end.
    destruct Hk as [-> | [K1 K2]]; [| exfalso; clear - PAL K1 K2; Z.div_mod_to_equations; lia].
    step. step. lit_branch. clear SHR HACC.
    zstep. rewrite (sx32_lit 0) by lia.
    unfold exitstA in K.
    zstep. zstep. zstep. step. lit_branch. apply K.
  Qed.
End PE2.
End W.
